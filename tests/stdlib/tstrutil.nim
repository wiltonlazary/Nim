discard """
  output: "ha/home/a1xyz/usr/bin"
"""
# test the new strutils module

import
  strutils

import macros

template rejectParse(e) =
  try:
    discard e
    raise newException(AssertionError, "This was supposed to fail: $#!" % astToStr(e))
  except ValueError: discard

proc testStrip() =
  write(stdout, strip("  ha  "))

proc testRemoveSuffix =
  var s = "hello\n\r"
  s.removeSuffix
  assert s == "hello"
  s.removeSuffix
  assert s == "hello"

  s = "hello\n\n"
  s.removeSuffix
  assert s == "hello"

  s = "hello\r"
  s.removeSuffix
  assert s == "hello"

  s = "hello \n there"
  s.removeSuffix
  assert s == "hello \n there"

  s = "hello"
  s.removeSuffix("llo")
  assert s == "he"
  s.removeSuffix('e')
  assert s == "h"

  s = "hellos"
  s.removeSuffix({'s','z'})
  assert s == "hello"
  s.removeSuffix({'l','o'})
  assert s == "he"

  s = "aeiou"
  s.removeSuffix("")
  assert s == "aeiou"

  s = ""
  s.removeSuffix("")
  assert s == ""

  s = "  "
  s.removeSuffix
  assert s == "  "

  s = "  "
  s.removeSuffix("")
  assert s == "  "

  s = "    "
  s.removeSuffix(" ")
  assert s == "   "

  s = "    "
  s.removeSuffix(' ')
  assert s == ""

  # Contrary to Chomp in other languages
  # empty string does not change behaviour
  s = "hello\r\n\r\n"
  s.removeSuffix("")
  assert s == "hello\r\n\r\n"

proc testRemovePrefix =
  var s = "\n\rhello"
  s.removePrefix
  assert s == "hello"
  s.removePrefix
  assert s == "hello"

  s = "\n\nhello"
  s.removePrefix
  assert s == "hello"

  s = "\rhello"
  s.removePrefix
  assert s == "hello"

  s = "hello \n there"
  s.removePrefix
  assert s == "hello \n there"

  s = "hello"
  s.removePrefix("hel")
  assert s == "lo"
  s.removePrefix('l')
  assert s == "o"

  s = "hellos"
  s.removePrefix({'h','e'})
  assert s == "llos"
  s.removePrefix({'l','o'})
  assert s == "s"

  s = "aeiou"
  s.removePrefix("")
  assert s == "aeiou"

  s = ""
  s.removePrefix("")
  assert s == ""

  s = "  "
  s.removePrefix
  assert s == "  "

  s = "  "
  s.removePrefix("")
  assert s == "  "

  s = "    "
  s.removePrefix(" ")
  assert s == "   "

  s = "    "
  s.removePrefix(' ')
  assert s == ""

  # Contrary to Chomp in other languages
  # empty string does not change behaviour
  s = "\r\n\r\nhello"
  s.removePrefix("")
  assert s == "\r\n\r\nhello"

proc main() =
  testStrip()
  testRemoveSuffix()
  testRemovePrefix()
  for p in split("/home/a1:xyz:/usr/bin", {':'}):
    write(stdout, p)

proc testDelete =
  var s = "0123456789ABCDEFGH"
  delete(s, 4, 5)
  assert s == "01236789ABCDEFGH"
  delete(s, s.len-1, s.len-1)
  assert s == "01236789ABCDEFG"
  delete(s, 0, 0)
  assert s == "1236789ABCDEFG"

proc testFind =
  assert "0123456789ABCDEFGH".find('A') == 10
  assert "0123456789ABCDEFGH".find('A', 5) == 10
  assert "0123456789ABCDEFGH".find('A', 5, 10) == 10
  assert "0123456789ABCDEFGH".find('A', 5, 9) == -1
  assert "0123456789ABCDEFGH".find("A") == 10
  assert "0123456789ABCDEFGH".find("A", 5) == 10
  assert "0123456789ABCDEFGH".find("A", 5, 10) == 10
  assert "0123456789ABCDEFGH".find("A", 5, 9) == -1
  assert "0123456789ABCDEFGH".find({'A'..'C'}) == 10
  assert "0123456789ABCDEFGH".find({'A'..'C'}, 5) == 10
  assert "0123456789ABCDEFGH".find({'A'..'C'}, 5, 10) == 10
  assert "0123456789ABCDEFGH".find({'A'..'C'}, 5, 9) == -1

proc testRFind =
  assert "0123456789ABCDEFGAH".rfind('A') == 17
  assert "0123456789ABCDEFGAH".rfind('A', last=13) == 10
  assert "0123456789ABCDEFGAH".rfind('H', last=13) == -1
  assert "0123456789ABCDEFGAH".rfind("A") == 17
  assert "0123456789ABCDEFGAH".rfind("A", last=13) == 10
  assert "0123456789ABCDEFGAH".rfind("H", last=13) == -1
  assert "0123456789ABCDEFGAH".rfind({'A'..'C'}) == 17
  assert "0123456789ABCDEFGAH".rfind({'A'..'C'}, last=13) == 12
  assert "0123456789ABCDEFGAH".rfind({'G'..'H'}, last=13) == -1
  assert "0123456789ABCDEFGAH".rfind('A', start=18) == -1
  assert "0123456789ABCDEFGAH".rfind('A', start=11, last=17) == 17
  assert "0123456789ABCDEFGAH".rfind("0", start=0) == 0
  assert "0123456789ABCDEFGAH".rfind("0", start=1) == -1
  assert "0123456789ABCDEFGAH".rfind("H", start=11) == 18
  assert "0123456789ABCDEFGAH".rfind({'0'..'9'}, start=5) == 9
  assert "0123456789ABCDEFGAH".rfind({'0'..'9'}, start=10) == -1

proc testTrimZeros() =
  var x = "1200"
  x.trimZeros()
  assert x == "1200"
  x = "120.0"
  x.trimZeros()
  assert x == "120"
  x = "0."
  x.trimZeros()
  assert x == "0"
  x = "1.0e2"
  x.trimZeros()
  assert x == "1e2"
  x = "78.90"
  x.trimZeros()
  assert x == "78.9"
  x = "1.23e4"
  x.trimZeros()
  assert x == "1.23e4"
  x = "1.01"
  x.trimZeros()
  assert x == "1.01"
  x = "1.1001"
  x.trimZeros()
  assert x == "1.1001"
  x = "0.0"
  x.trimZeros()
  assert x == "0"
  x = "0.01"
  x.trimZeros()
  assert x == "0.01"
  x = "1e0"
  x.trimZeros()
  assert x == "1e0"

proc testSplitLines() =
  let fixture = "a\nb\rc\r\nd"
  assert len(fixture.splitLines) == 4
  assert splitLines(fixture) == @["a", "b", "c", "d"]
  assert splitLines(fixture, keepEol=true) == @["a\n", "b\r", "c\r\n", "d"]

proc testCountLines =
  proc assertCountLines(s: string) = assert s.countLines == s.splitLines.len
  assertCountLines("")
  assertCountLines("\n")
  assertCountLines("\n\n")
  assertCountLines("abc")
  assertCountLines("abc\n123")
  assertCountLines("abc\n123\n")
  assertCountLines("\nabc\n123")
  assertCountLines("\nabc\n123\n")

proc testParseInts =
  # binary
  assert "0b1111".parseBinInt == 15
  assert "0B1111".parseBinInt == 15
  assert "1111".parseBinInt == 15
  assert "1110".parseBinInt == 14
  assert "1_1_1_1".parseBinInt == 15
  assert "0b1_1_1_1".parseBinInt == 15
  rejectParse "".parseBinInt
  rejectParse "_".parseBinInt
  rejectParse "0b".parseBinInt
  rejectParse "0b1234".parseBinInt
  # hex
  assert "0x72".parseHexInt == 114
  assert "0X72".parseHexInt == 114
  assert "#72".parseHexInt == 114
  assert "72".parseHexInt == 114
  assert "FF".parseHexInt == 255
  assert "ff".parseHexInt == 255
  assert "fF".parseHexInt == 255
  assert "0x7_2".parseHexInt == 114
  rejectParse "".parseHexInt
  rejectParse "_".parseHexInt
  rejectParse "0x".parseHexInt
  rejectParse "0xFFG".parseHexInt
  rejectParse "reject".parseHexInt
  # octal
  assert "0o17".parseOctInt == 15
  assert "0O17".parseOctInt == 15
  assert "17".parseOctInt == 15
  assert "10".parseOctInt == 8
  assert "0o1_0_0".parseOctInt == 64
  rejectParse "".parseOctInt
  rejectParse "_".parseOctInt
  rejectParse "0o".parseOctInt
  rejectParse "9".parseOctInt
  rejectParse "0o9".parseOctInt
  rejectParse "reject".parseOctInt

testDelete()
testFind()
testRFind()
testTrimZeros()
testSplitLines()
testCountLines()
testParseInts()

assert(insertSep($1000_000) == "1_000_000")
assert(insertSep($232) == "232")
assert(insertSep($12345, ',') == "12,345")
assert(insertSep($0) == "0")

assert "/1/2/3".rfind('/') == 4
assert "/1/2/3".rfind('/', last=1) == 0
assert "/1/2/3".rfind('0') == -1

assert(toHex(100i16, 32) == "00000000000000000000000000000064")
assert(toHex(-100i16, 32) == "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFF9C")

assert "".parseHexStr == ""
assert "00Ff80".parseHexStr == "\0\xFF\x80"
try:
  discard "00Ff8".parseHexStr
  assert false, "Should raise ValueError"
except ValueError:
  discard

try:
  discard "0k".parseHexStr
  assert false, "Should raise ValueError"
except ValueError:
  discard

assert "".toHex == ""
assert "\x00\xFF\x80".toHex == "00FF80"
assert "0123456789abcdef".parseHexStr.toHex == "0123456789ABCDEF"

assert(' '.repeat(8) == "        ")
assert(" ".repeat(8) == "        ")
assert(spaces(8) == "        ")

assert(' '.repeat(0) == "")
assert(" ".repeat(0) == "")
assert(spaces(0) == "")

# bug #11369

var num: int64 = -1
assert num.toBin(64) == "1111111111111111111111111111111111111111111111111111111111111111"
assert num.toOct(24) == "001777777777777777777777"


# bug #8911
when true:
  static:
    let a = ""
    let a2 = a.replace("\n", "\\n")

when true:
  static:
    let b = "b"
    let b2 = b.replace("\n", "\\n")

when true:
  let c = ""
  let c2 = c.replace("\n", "\\n")

main()
#OUT ha/home/a1xyz/usr/bin
