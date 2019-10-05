#
#
#            Nim's Runtime Library
#        (c) Copyright 2017 Nim contributors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#


# import typetraits
# strs already imported allocators for us.

proc supportsCopyMem(t: typedesc): bool {.magic: "TypeTrait".}

## Default seq implementation used by Nim's core.
type
  NimSeqPayload[T] = object
    cap: int
    allocator: Allocator
    data: UncheckedArray[T]

  NimSeqV2*[T] = object
    len: int
    p: ptr NimSeqPayload[T]

const nimSeqVersion {.core.} = 2

template payloadSize(cap): int = cap * sizeof(T) + sizeof(int) + sizeof(Allocator)

# XXX make code memory safe for overflows in '*'

when false:
  # this is currently not part of Nim's type bound operators and so it's
  # built into the tracing proc generation just like before.
  proc `=trace`[T](s: NimSeqV2[T]) =
    for i in 0 ..< s.len: `=trace`(s.data[i])

#[
Keep in mind that C optimizers are bad at detecting the connection
between ``s.p != nil`` and ``s.len != 0`` and that these are intermingled
with user-level code that accesses ``s.len`` only, never ``s.p`` directly.
This means the check for whether ``s.p`` needs to be freed should
be ``s.len == 0`` even though that feels slightly more awkward.
]#

when not defined(nimV2):
  proc `=destroy`[T](s: var seq[T]) =
    var x = cast[ptr NimSeqV2[T]](addr s)
    var p = x.p
    if p != nil:
      mixin `=destroy`
      when not supportsCopyMem(T):
        for i in 0..<x.len: `=destroy`(p.data[i])
      if p.allocator != nil:
        p.allocator.dealloc(p.allocator, p, payloadSize(p.cap))
      x.p = nil
      x.len = 0

  proc `=`[T](x: var seq[T]; y: seq[T]) =
    mixin `=destroy`
    var a = cast[ptr NimSeqV2[T]](addr x)
    var b = cast[ptr NimSeqV2[T]](unsafeAddr y)

    if a.p == b.p: return
    `=destroy`(x)
    a.len = b.len
    if b.p != nil:
      a.p = cast[type(a.p)](alloc(payloadSize(a.len)))
      when supportsCopyMem(T):
        if a.len > 0:
          copyMem(unsafeAddr a.p.data[0], unsafeAddr b.p.data[0], a.len * sizeof(T))
      else:
        for i in 0..<a.len:
          a.p.data[i] = b.p.data[i]

  proc `=sink`[T](x: var seq[T]; y: seq[T]) =
    mixin `=destroy`
    var a = cast[ptr NimSeqV2[T]](addr x)
    var b = cast[ptr NimSeqV2[T]](unsafeAddr y)
    if a.p != nil and a.p != b.p:
      `=destroy`(x)
    a.len = b.len
    a.p = b.p


type
  PayloadBase = object
    cap: int
    allocator: Allocator

proc newSeqPayload(cap, elemSize: int): pointer {.compilerRtl, raises: [].} =
  # we have to use type erasure here as Nim does not support generic
  # compilerProcs. Oh well, this will all be inlined anyway.
  if cap > 0:
    let allocator = getLocalAllocator()
    var p = cast[ptr PayloadBase](allocator.alloc(allocator, cap * elemSize + sizeof(int) + sizeof(Allocator)))
    p.allocator = allocator
    p.cap = cap
    result = p
  else:
    result = nil

proc prepareSeqAdd(len: int; p: pointer; addlen, elemSize: int): pointer {.
    compilerRtl, noSideEffect, raises: [].} =
  {.noSideEffect.}:
    template `+!`(p: pointer, s: int): pointer =
      cast[pointer](cast[int](p) +% s)

    const headerSize = sizeof(int) + sizeof(Allocator)
    if addlen <= 0:
      result = p
    elif p == nil:
      result = newSeqPayload(len+addlen, elemSize)
    else:
      # Note: this means we cannot support things that have internal pointers as
      # they get reallocated here. This needs to be documented clearly.
      var p = cast[ptr PayloadBase](p)
      let cap = max(resize(p.cap), len+addlen)
      if p.allocator == nil:
        let allocator = getLocalAllocator()
        var q = cast[ptr PayloadBase](allocator.alloc(allocator,
          headerSize + elemSize * cap))
        copyMem(q +! headerSize, p +! headerSize, len * elemSize)
        q.allocator = allocator
        q.cap = cap
        result = q
      else:
        let allocator = p.allocator
        var q = cast[ptr PayloadBase](allocator.realloc(allocator, p,
          headerSize + elemSize * p.cap,
          headerSize + elemSize * cap))
        q.allocator = allocator
        q.cap = cap
        result = q

proc shrink*[T](x: var seq[T]; newLen: Natural) =
  mixin `=destroy`
  sysAssert newLen <= x.len, "invalid newLen parameter for 'shrink'"
  when not supportsCopyMem(T):
    for i in countdown(x.len - 1, newLen):
      `=destroy`(x[i])
  # XXX This is wrong for const seqs that were moved into 'x'!
  cast[ptr NimSeqV2[T]](addr x).len = newLen

proc grow*[T](x: var seq[T]; newLen: Natural; value: T) =
  let oldLen = x.len
  if newLen <= oldLen: return
  var xu = cast[ptr NimSeqV2[T]](addr x)
  if xu.p == nil or xu.p.cap < newLen:
    xu.p = cast[typeof(xu.p)](prepareSeqAdd(oldLen, xu.p, newLen - oldLen, sizeof(T)))
  xu.len = newLen
  for i in oldLen .. newLen-1:
    xu.p.data[i] = value

proc add*[T](x: var seq[T]; value: sink T) {.magic: "AppendSeqElem", noSideEffect.} =
  ## Generic proc for adding a data item `y` to a container `x`.
  ##
  ## For containers that have an order, `add` means *append*. New generic
  ## containers should also call their adding proc `add` for consistency.
  ## Generic code becomes much easier to write if the Nim naming scheme is
  ## respected.
  let oldLen = x.len
  var xu = cast[ptr NimSeqV2[T]](addr x)
  if xu.p == nil or xu.p.cap < oldLen+1:
    xu.p = cast[typeof(xu.p)](prepareSeqAdd(oldLen, xu.p, 1, sizeof(T)))
  xu.len = oldLen+1
  xu.p.data[oldLen] = value

proc setLen[T](s: var seq[T], newlen: Natural) =
  {.noSideEffect.}:
    if newlen < s.len:
      shrink(s, newlen)
    else:
      let oldLen = s.len
      if newlen <= oldLen: return
      var xu = cast[ptr NimSeqV2[T]](addr s)
      if xu.p == nil or xu.p.cap < newlen:
        xu.p = cast[typeof(xu.p)](prepareSeqAdd(oldLen, xu.p, newlen - oldLen, sizeof(T)))
      xu.len = newlen

when false:
  proc resize[T](s: var NimSeqV2[T]) =
    let old = s.cap
    if old == 0: s.cap = 8
    else: s.cap = (s.cap * 3) shr 1
    s.data = cast[type(s.data)](realloc(s.data, old * sizeof(T), s.cap * sizeof(T)))

  proc reserveSlot[T](x: var NimSeqV2[T]): ptr T =
    if x.len >= x.cap: resize(x)
    result = addr(x.data[x.len])
    inc x.len

  template add*[T](x: var NimSeqV2[T]; y: T) =
    reserveSlot(x)[] = y

  template `[]`*[T](x: NimSeqV2[T]; i: Natural): T =
    assert i < x.len
    x.data[i]

  template `[]=`*[T](x: NimSeqV2[T]; i: Natural; y: T) =
    assert i < x.len
    x.data[i] = y

  proc `@`*[T](elems: sink openArray[T]): NimSeqV2[T] =
    result.cap = elems.len
    result.len = elems.len
    result.data = cast[type(result.data)](alloc(result.cap * sizeof(T)))
    when supportsCopyMem(T):
      copyMem(result.data, unsafeAddr(elems[0]), result.cap * sizeof(T))
    else:
      for i in 0..<result.len:
        result.data[i] = elems[i]
