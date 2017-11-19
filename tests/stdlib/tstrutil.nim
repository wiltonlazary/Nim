discard """
  file: "tstrutil.nim"
  output: "ha/home/a1xyz/usr/bin"
"""
# test the new strutils module

import
  strutils

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


proc testIsAlphaNumeric =
  assert isAlphaNumeric("abcdABC1234") == true
  assert isAlphaNumeric("a") == true
  assert isAlphaNumeric("abcABC?1234") == false
  assert isAlphaNumeric("abcABC 1234") == false
  assert isAlphaNumeric(".") == false

testIsAlphaNumeric()

proc testIsDigit =
  assert isDigit("1") == true
  assert isDigit("1234") == true
  assert isDigit("abcABC?1234") == false
  assert isDigit(".") == false
  assert isDigit(":") == false

testIsDigit()

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
  assert "0123456789ABCDEFGAH".rfind('A', 13) == 10
  assert "0123456789ABCDEFGAH".rfind('H', 13) == -1
  assert "0123456789ABCDEFGAH".rfind("A") == 17
  assert "0123456789ABCDEFGAH".rfind("A", 13) == 10
  assert "0123456789ABCDEFGAH".rfind("H", 13) == -1
  assert "0123456789ABCDEFGAH".rfind({'A'..'C'}) == 17
  assert "0123456789ABCDEFGAH".rfind({'A'..'C'}, 13) == 12
  assert "0123456789ABCDEFGAH".rfind({'G'..'H'}, 13) == -1

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

testDelete()
testFind()
testRFind()
testCountLines()

assert(insertSep($1000_000) == "1_000_000")
assert(insertSep($232) == "232")
assert(insertSep($12345, ',') == "12,345")
assert(insertSep($0) == "0")

assert(editDistance("prefix__hallo_suffix", "prefix__hallo_suffix") == 0)
assert(editDistance("prefix__hallo_suffix", "prefix__hallo_suffi1") == 1)
assert(editDistance("prefix__hallo_suffix", "prefix__HALLO_suffix") == 5)
assert(editDistance("prefix__hallo_suffix", "prefix__ha_suffix") == 3)
assert(editDistance("prefix__hallo_suffix", "prefix") == 14)
assert(editDistance("prefix__hallo_suffix", "suffix") == 14)
assert(editDistance("prefix__hallo_suffix", "prefix__hao_suffix") == 2)
assert(editDistance("main", "malign") == 2)

assert "/1/2/3".rfind('/') == 4
assert "/1/2/3".rfind('/', 1) == 0
assert "/1/2/3".rfind('0') == -1

assert(toHex(100i16, 32) == "00000000000000000000000000000064")
assert(toHex(-100i16, 32) == "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFF9C")

assert(' '.repeat(8)== "        ")
assert(" ".repeat(8) == "        ")
assert(spaces(8) == "        ")

assert(' '.repeat(0) == "")
assert(" ".repeat(0) == "")
assert(spaces(0) == "")

main()
#OUT ha/home/a1xyz/usr/bin
