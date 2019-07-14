discard """
  output: '''(x: 'a')'''
"""

type
  Bar[T] = object
    x: T

proc infer(T: typeDesc): Bar[T] = Bar[T](x: 'a')

let foo = infer(char)
echo foo

when true:
  # bug #1783

  type
      uoffset_t* = uint32
      FlatBufferBuilder* = object

      Array* [T] = object
          o*: uoffset_t
          len*: int
          data*: ptr UncheckedArray[T]

  proc ca* (fbb: ptr FlatBufferBuilder, T: typedesc, len: int): Array[T] {.noinit.} =
      result.len = len

  var fbb: ptr FlatBufferBuilder
  let boolarray = ca(fbb, bool, 2)
  let boolarray2 = fbb.ca(bool, 2)

# bug #1664
type Point[T] = tuple[x, y: T]
proc origin(T: typedesc): Point[T] = discard
discard origin(int)

# https://github.com/nim-lang/Nim/issues/7516
import typetraits

proc hasDefault1(T: type = int): auto = return T.name
doAssert hasDefault1(int) == "int"
doAssert hasDefault1(string) == "string"
doAssert hasDefault1() == "int"

proc hasDefault2(T = string): auto = return T.name
doAssert hasDefault2(int) == "int"
doAssert hasDefault2(string) == "string"
doAssert hasDefault2() == "string"

