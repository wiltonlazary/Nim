#
#
#            Nim's Runtime Library
#        (c) Copyright 2012 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements efficient computations of hash values for diverse
## Nim types. All the procs are based on these two building blocks:
## - `!& proc <#!&,Hash,int>`_ used to start or mix a hash value, and
## - `!$ proc <#!$,Hash>`_ used to *finish* the hash value.
##
## If you want to implement hash procs for your custom types,
## you will end up writing the following kind of skeleton of code:
##
## .. code-block:: Nim
##  proc hash(x: Something): Hash =
##    ## Computes a Hash from `x`.
##    var h: Hash = 0
##    # Iterate over parts of `x`.
##    for xAtom in x:
##      # Mix the atom with the partial hash.
##      h = h !& xAtom
##    # Finish the hash.
##    result = !$h
##
## If your custom types contain fields for which there already is a hash proc,
## like for example objects made up of ``strings``, you can simply hash
## together the hash value of the individual fields:
##
## .. code-block:: Nim
##  proc hash(x: Something): Hash =
##    ## Computes a Hash from `x`.
##    var h: Hash = 0
##    h = h !& hash(x.foo)
##    h = h !& hash(x.bar)
##    result = !$h
##
## **See also:**
## * `md5 module <md5.html>`_ for MD5 checksum algorithm
## * `base64 module <base64.html>`_ for a base64 encoder and decoder
## * `std/sha1 module <sha1.html>`_ for a sha1 encoder and decoder
## * `tables module <tables.html>`_ for hash tables


import
  strutils

type
  Hash* = int  ## A hash value. Hash tables using these values should
               ## always have a size of a power of two and can use the ``and``
               ## operator instead of ``mod`` for truncation of the hash value.

const
  IntSize = sizeof(int)

proc `!&`*(h: Hash, val: int): Hash {.inline.} =
  ## Mixes a hash value `h` with `val` to produce a new hash value.
  ##
  ## This is only needed if you need to implement a hash proc for a new datatype.
  let h = cast[uint](h)
  let val = cast[uint](val)
  var res = h + val
  res = res + res shl 10
  res = res xor (res shr 6)
  result = cast[Hash](res)

proc `!$`*(h: Hash): Hash {.inline.} =
  ## Finishes the computation of the hash value.
  ##
  ## This is only needed if you need to implement a hash proc for a new datatype.
  let h = cast[uint](h) # Hash is practically unsigned.
  var res = h + h shl 3
  res = res xor (res shr 11)
  res = res + res shl 15
  result = cast[Hash](res)

proc hashData*(data: pointer, size: int): Hash =
  ## Hashes an array of bytes of size `size`.
  var h: Hash = 0
  when defined(js):
    var p: cstring
    asm """`p` = `Data`;"""
  else:
    var p = cast[cstring](data)
  var i = 0
  var s = size
  while s > 0:
    h = h !& ord(p[i])
    inc(i)
    dec(s)
  result = !$h

when defined(js):
  var objectID = 0

proc hash*(x: pointer): Hash {.inline.} =
  ## Efficient hashing of pointers.
  when defined(js):
    asm """
      if (typeof `x` == "object") {
        if ("_NimID" in `x`)
          `result` = `x`["_NimID"];
        else {
          `result` = ++`objectID`;
          `x`["_NimID"] = `result`;
        }
      }
    """
  else:
    result = cast[Hash](cast[uint](x) shr 3) # skip the alignment

when not defined(booting):
  proc hash*[T: proc](x: T): Hash {.inline.} =
    ## Efficient hashing of proc vars. Closures are supported too.
    when T is "closure":
      result = hash(rawProc(x)) !& hash(rawEnv(x))
    else:
      result = hash(pointer(x))

proc hash*(x: int): Hash {.inline.} =
  ## Efficient hashing of integers.
  result = x

proc hash*(x: int64): Hash {.inline.} =
  ## Efficient hashing of `int64` integers.
  result = toU32(x)

proc hash*(x: uint): Hash {.inline.} =
  ## Efficient hashing of unsigned integers.
  result = cast[int](x)

proc hash*(x: uint64): Hash {.inline.} =
  ## Efficient hashing of `uint64` integers.
  result = toU32(cast[int](x))

proc hash*(x: char): Hash {.inline.} =
  ## Efficient hashing of characters.
  result = ord(x)

proc hash*[T: Ordinal](x: T): Hash {.inline.} =
  ## Efficient hashing of other ordinal types (e.g. enums).
  result = ord(x)

proc hash*(x: float): Hash {.inline.} =
  ## Efficient hashing of floats.
  var y = x + 1.0
  result = cast[ptr Hash](addr(y))[]


# Forward declarations before methods that hash containers. This allows
# containers to contain other containers
proc hash*[A](x: openArray[A]): Hash
proc hash*[A](x: set[A]): Hash

template bytewiseHashing(result: Hash, x: typed, start, stop: int) =
  for i in start .. stop:
    result = result !& hash(x[i])
  result = !$result

template hashImpl(result: Hash, x: typed, start, stop: int) =
  let
    elementSize = sizeof(x[start])
    stepSize = IntSize div elementSize
  var i = start
  while i <= stop+1 - stepSize:
    var n = 0
    when nimvm:
      # we cannot cast in VM, so we do it manually
      for j in countdown(stepSize-1, 0):
        n = (n shl (8*elementSize)) or ord(x[i+j])
    else:
      n = cast[ptr Hash](unsafeAddr x[i])[]
    result = result !& n
    i += stepSize
  bytewiseHashing(result, x, i, stop) # hash the remaining elements and finish

proc hash*(x: string): Hash =
  ## Efficient hashing of strings.
  ##
  ## See also:
  ## * `hashIgnoreStyle <#hashIgnoreStyle,string>`_
  ## * `hashIgnoreCase <#hashIgnoreCase,string>`_
  runnableExamples:
    doAssert hash("abracadabra") != hash("AbracadabrA")

  hashImpl(result, x, 0, high(x))

proc hash*(x: cstring): Hash =
  ## Efficient hashing of null-terminated strings.
  runnableExamples:
    doAssert hash(cstring"abracadabra") == hash("abracadabra")
    doAssert hash(cstring"AbracadabrA") == hash("AbracadabrA")
    doAssert hash(cstring"abracadabra") != hash(cstring"AbracadabrA")

  hashImpl(result, x, 0, high(x))

proc hash*(sBuf: string, sPos, ePos: int): Hash =
  ## Efficient hashing of a string buffer, from starting
  ## position `sPos` to ending position `ePos` (included).
  ##
  ## ``hash(myStr, 0, myStr.high)`` is equivalent to ``hash(myStr)``.
  runnableExamples:
    var a = "abracadabra"
    doAssert hash(a, 0, 3) == hash(a, 7, 10)

  hashImpl(result, sBuf, sPos, ePos)

proc hashIgnoreStyle*(x: string): Hash =
  ## Efficient hashing of strings; style is ignored.
  ##
  ## **Note:** This uses different hashing algorithm than `hash(string)`.
  ##
  ## See also:
  ## * `hashIgnoreCase <#hashIgnoreCase,string>`_
  runnableExamples:
    doAssert hashIgnoreStyle("aBr_aCa_dAB_ra") == hashIgnoreStyle("abracadabra")
    doAssert hashIgnoreStyle("abcdefghi") != hash("abcdefghi")

  var h: Hash = 0
  var i = 0
  let xLen = x.len
  while i < xLen:
    var c = x[i]
    if c == '_':
      inc(i)
    else:
      if c in {'A'..'Z'}:
        c = chr(ord(c) + (ord('a') - ord('A'))) # toLower()
      h = h !& ord(c)
      inc(i)
  result = !$h

proc hashIgnoreStyle*(sBuf: string, sPos, ePos: int): Hash =
  ## Efficient hashing of a string buffer, from starting
  ## position `sPos` to ending position `ePos` (included); style is ignored.
  ##
  ## **Note:** This uses different hashing algorithm than `hash(string)`.
  ##
  ## ``hashIgnoreStyle(myBuf, 0, myBuf.high)`` is equivalent
  ## to ``hashIgnoreStyle(myBuf)``.
  runnableExamples:
    var a = "ABracada_b_r_a"
    doAssert hashIgnoreStyle(a, 0, 3) == hashIgnoreStyle(a, 7, a.high)

  var h: Hash = 0
  var i = sPos
  while i <= ePos:
    var c = sBuf[i]
    if c == '_':
      inc(i)
    else:
      if c in {'A'..'Z'}:
        c = chr(ord(c) + (ord('a') - ord('A'))) # toLower()
      h = h !& ord(c)
      inc(i)
  result = !$h

proc hashIgnoreCase*(x: string): Hash =
  ## Efficient hashing of strings; case is ignored.
  ##
  ## **Note:** This uses different hashing algorithm than `hash(string)`.
  ##
  ## See also:
  ## * `hashIgnoreStyle <#hashIgnoreStyle,string>`_
  runnableExamples:
    doAssert hashIgnoreCase("ABRAcaDABRA") == hashIgnoreCase("abRACAdabra")
    doAssert hashIgnoreCase("abcdefghi") != hash("abcdefghi")

  var h: Hash = 0
  for i in 0..x.len-1:
    var c = x[i]
    if c in {'A'..'Z'}:
      c = chr(ord(c) + (ord('a') - ord('A'))) # toLower()
    h = h !& ord(c)
  result = !$h

proc hashIgnoreCase*(sBuf: string, sPos, ePos: int): Hash =
  ## Efficient hashing of a string buffer, from starting
  ## position `sPos` to ending position `ePos` (included); case is ignored.
  ##
  ## **Note:** This uses different hashing algorithm than `hash(string)`.
  ##
  ## ``hashIgnoreCase(myBuf, 0, myBuf.high)`` is equivalent
  ## to ``hashIgnoreCase(myBuf)``.
  runnableExamples:
    var a = "ABracadabRA"
    doAssert hashIgnoreCase(a, 0, 3) == hashIgnoreCase(a, 7, 10)

  var h: Hash = 0
  for i in sPos..ePos:
    var c = sBuf[i]
    if c in {'A'..'Z'}:
      c = chr(ord(c) + (ord('a') - ord('A'))) # toLower()
    h = h !& ord(c)
  result = !$h


proc hash*[T: tuple](x: T): Hash =
  ## Efficient hashing of tuples.
  for f in fields(x):
    result = result !& hash(f)
  result = !$result

proc hash*[A](x: openArray[A]): Hash =
  ## Efficient hashing of arrays and sequences.
  when A is char|SomeInteger:
    hashImpl(result, x, 0, x.high)
  else:
    bytewiseHashing(result, x, 0, x.high)

proc hash*[A](aBuf: openArray[A], sPos, ePos: int): Hash =
  ## Efficient hashing of portions of arrays and sequences, from starting
  ## position `sPos` to ending position `ePos` (included).
  ##
  ## ``hash(myBuf, 0, myBuf.high)`` is equivalent to ``hash(myBuf)``.
  runnableExamples:
    let a = [1, 2, 5, 1, 2, 6]
    doAssert hash(a, 0, 1) == hash(a, 3, 4)

  when A is char|SomeInteger:
    hashImpl(result, aBuf, sPos, ePos)
  else:
    bytewiseHashing(result, aBuf, sPos, ePos)

proc hash*[A](x: set[A]): Hash =
  ## Efficient hashing of sets.
  for it in items(x):
    result = result !& hash(it)
  result = !$result


when isMainModule:
  block empty:
    var
      a = ""
      b = newSeq[char]()
      c = newSeq[int]()
    doAssert hash(a) == 0
    doAssert hash(b) == 0
    doAssert hash(c) == 0
    doAssert hashIgnoreCase(a) == 0
    doAssert hashIgnoreStyle(a) == 0
  block sameButDifferent:
    doAssert hash("aa bb aaaa1234") == hash("aa bb aaaa1234", 0, 13)
    doAssert hash("aa bb aaaa1234") == hash(cstring"aa bb aaaa1234")
    doAssert hashIgnoreCase("aA bb aAAa1234") == hashIgnoreCase("aa bb aaaa1234")
    doAssert hashIgnoreStyle("aa_bb_AAaa1234") == hashIgnoreCase("aaBBAAAa1234")
  block smallSize: # no multibyte hashing
    let
      xx = @['H','e','l','l','o']
      ii = @[72'i8, 101, 108, 108, 111]
      ss = "Hello"
    doAssert hash(xx) == hash(ii)
    doAssert hash(xx) == hash(ss)
    doAssert hash(xx) == hash(xx, 0, xx.high)
    doAssert hash(ss) == hash(ss, 0, ss.high)
  block largeSize: # longer than 8 characters, should trigger multibyte hashing
    let
      xx = @['H','e','l','l','o']
      xxl = @['H','e','l','l','o','w','e','e','n','s']
      ssl = "Helloweens"
    doAssert hash(xxl) == hash(ssl)
    doAssert hash(xxl) == hash(xxl, 0, xxl.high)
    doAssert hash(ssl) == hash(ssl, 0, ssl.high)
    doAssert hash(xx) == hash(xxl, 0, 4)
  block misc:
    let
      a = [1'u8, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4]
      b = [1'i8, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4]
    doAssert hash(a) == hash(b)
    doAssert hash(a, 2, 5) == hash(b, 2, 5)
