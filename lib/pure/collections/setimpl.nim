#
#
#            Nim's Runtime Library
#        (c) Copyright 2019 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# An ``include`` file for the different hash set implementations.


template maxHash(t): untyped = high(t.data)
template dataLen(t): untyped = len(t.data)

include hashcommon

template initImpl(s: typed, size: int) =
  assert isPowerOfTwo(size)
  when s is OrderedSet:
    s.first = -1
    s.last = -1
  s.counter = 0
  newSeq(s.data, size)

template rawInsertImpl() {.dirty.} =
  if data.len == 0:
    initImpl(s, defaultInitialSize)
  data[h].key = key
  data[h].hcode = hc

proc rawInsert[A](s: var HashSet[A], data: var KeyValuePairSeq[A], key: A,
                  hc: Hash, h: Hash) =
  rawInsertImpl()

proc enlarge[A](s: var HashSet[A]) =
  var n: KeyValuePairSeq[A]
  newSeq(n, len(s.data) * growthFactor)
  swap(s.data, n) # n is now old seq
  for i in countup(0, high(n)):
    if isFilledAndValid(n[i].hcode):
      var j = -1 - rawGetKnownHC(s, n[i].key, n[i].hcode)
      rawInsert(s, s.data, n[i].key, n[i].hcode, j)

template inclImpl() {.dirty.} =
  if s.data.len == 0:
    initImpl(s, defaultInitialSize)
  var hc: Hash
  var index = rawGet(s, key, hc)
  if index < 0:
    if mustRehash(s):
      enlarge(s)
      index = rawGetKnownHC(s, key, hc)
    rawInsert(s, s.data, key, hc, -1 - index)
    inc(s.counter)

template containsOrInclImpl() {.dirty.} =
  if s.data.len == 0:
    initImpl(s, defaultInitialSize)
  var hc: Hash
  var index = rawGet(s, key, hc)
  if index >= 0:
    result = true
  else:
    if mustRehash(s):
      enlarge(s)
      index = rawGetKnownHC(s, key, hc)
    rawInsert(s, s.data, key, hc, -1 - index)
    inc(s.counter)

proc exclImpl[A](s: var HashSet[A], key: A): bool {.inline.} =
  var hc: Hash
  var i = rawGet(s, key, hc)
  var msk = high(s.data)
  result = true

  if i >= 0:
    result = false
    dec(s.counter)
    inc(s.countDeleted)
    s.data[i].hcode = deletedMarker
    s.data[i].key = default(type(s.data[i].key))

template dollarImpl() {.dirty.} =
  result = "{"
  for key in items(s):
    if result.len > 1: result.add(", ")
    result.addQuoted(key)
  result.add("}")



# --------------------------- OrderedSet ------------------------------

proc rawGet[A](t: OrderedSet[A], key: A, hc: var Hash): int {.inline.} =
  rawGetImpl()

proc rawInsert[A](s: var OrderedSet[A], data: var OrderedKeyValuePairSeq[A],
                  key: A, hc: Hash, h: Hash) =
  rawInsertImpl()
  data[h].next = -1
  if s.first < 0: s.first = h
  if s.last >= 0: data[s.last].next = h
  s.last = h

proc enlarge[A](s: var OrderedSet[A]) =
  var n: OrderedKeyValuePairSeq[A]
  newSeq(n, len(s.data) * growthFactor)
  var h = s.first
  s.first = -1
  s.last = -1
  swap(s.data, n)
  while h >= 0:
    var nxt = n[h].next
    if isFilled(n[h].hcode): # should be isFilledAndValid once tombstones are used
      var j = -1 - rawGetKnownHC(s, n[h].key, n[h].hcode)
      rawInsert(s, s.data, n[h].key, n[h].hcode, j)
    h = nxt

proc exclImpl[A](s: var OrderedSet[A], key: A): bool {.inline.} =
  if len(s.data) == 0:
    return true
  var n: OrderedKeyValuePairSeq[A]
  newSeq(n, len(s.data))
  var h = s.first
  s.first = -1
  s.last = -1
  swap(s.data, n)
  let hc = genHash(key)
  result = true
  while h >= 0:
    var nxt = n[h].next
    if isFilled(n[h].hcode): # should be isFilledAndValid once tombstones are used
      if n[h].hcode == hc and n[h].key == key:
        dec s.counter
        result = false
      else:
        var j = -1 - rawGetKnownHC(s, n[h].key, n[h].hcode)
        rawInsert(s, s.data, n[h].key, n[h].hcode, j)
    h = nxt
