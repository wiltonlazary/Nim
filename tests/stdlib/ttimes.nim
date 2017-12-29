# test the new time module
discard """
  file: "ttimes.nim"
  output: '''[Suite] ttimes
'''
"""

import
  times, os, strutils, unittest

# $ date --date='@2147483647'
# Tue 19 Jan 03:14:07 GMT 2038

proc checkFormat(t: DateTime, format, expected: string) =
  let actual = t.format(format)
  if actual != expected:
    echo "Formatting failure!"
    echo "expected: ", expected
    echo "actual  : ", actual
    doAssert false

let t = fromUnix(2147483647).utc
t.checkFormat("ddd dd MMM hh:mm:ss yyyy", "Tue 19 Jan 03:14:07 2038")
t.checkFormat("ddd ddMMMhh:mm:ssyyyy", "Tue 19Jan03:14:072038")
t.checkFormat("d dd ddd dddd h hh H HH m mm M MM MMM MMMM s" &
  " ss t tt y yy yyy yyyy yyyyy z zz zzz",
  "19 19 Tue Tuesday 3 03 3 03 14 14 1 01 Jan January 7 07 A AM 8 38 038 2038 02038 +0 +00 +00:00")

t.checkFormat("yyyyMMddhhmmss", "20380119031407")

let t2 = fromUnix(160070789).utc # Mon 27 Jan 16:06:29 GMT 1975
t2.checkFormat("d dd ddd dddd h hh H HH m mm M MM MMM MMMM s" &
  " ss t tt y yy yyy yyyy yyyyy z zz zzz",
  "27 27 Mon Monday 4 04 16 16 6 06 1 01 Jan January 29 29 P PM 5 75 975 1975 01975 +0 +00 +00:00")

var t4 = fromUnix(876124714).utc # Mon  6 Oct 08:58:34 BST 1997
t4.checkFormat("M MM MMM MMMM", "10 10 Oct October")

# Interval tests
(t4 - initInterval(years = 2)).checkFormat("yyyy", "1995")
(t4 - initInterval(years = 7, minutes = 34, seconds = 24)).checkFormat("yyyy mm ss", "1990 24 10")

# checking dayOfWeek matches known days
doAssert getDayOfWeek(01, mJan, 0000) == dSat
doAssert getDayOfWeek(01, mJan, -0023) == dSat
doAssert getDayOfWeek(21, mSep, 1900) == dFri
doAssert getDayOfWeek(01, mJan, 1970) == dThu
doAssert getDayOfWeek(21, mSep, 1970) == dMon
doAssert getDayOfWeek(01, mJan, 2000) == dSat
doAssert getDayOfWeek(01, mJan, 2021) == dFri

# toUnix tests with GM timezone
let t4L = fromUnix(876124714).utc
doAssert toUnix(toTime(t4L)) == 876124714
doAssert toUnix(toTime(t4L)) + t4L.utcOffset == toUnix(toTime(t4))

# adding intervals
var
  a1L = toUnix(toTime(t4L + initInterval(hours = 1))) + t4L.utcOffset
  a1G = toUnix(toTime(t4)) + 60 * 60
doAssert a1L == a1G

# subtracting intervals
a1L = toUnix(toTime(t4L - initInterval(hours = 1))) + t4L.utcOffset
a1G = toUnix(toTime(t4)) - (60 * 60)
doAssert a1L == a1G

# add/subtract TimeIntervals and Time/TimeInfo
doAssert getTime() - 1.seconds == getTime() - 3.seconds + 2.seconds
doAssert getTime() + 65.seconds == getTime() + 1.minutes + 5.seconds
doAssert getTime() + 60.minutes == getTime() + 1.hours
doAssert getTime() + 24.hours == getTime() + 1.days
doAssert getTime() + 13.months == getTime() + 1.years + 1.months
var
  ti1 = getTime() + 1.years
ti1 -= 1.years
doAssert ti1 == getTime()
ti1 += 1.days
doAssert ti1 == getTime() + 1.days

# Bug with adding a day to a Time
let day = 24.hours
let tomorrow = getTime() + day
doAssert tomorrow - getTime() == 60*60*24

# Comparison between Time objects should be detected by compiler
# as 'noSideEffect'.
proc cmpTimeNoSideEffect(t1: Time, t2: Time): bool {.noSideEffect.} =
  result = t1 == t2
doAssert cmpTimeNoSideEffect(0.fromUnix, 0.fromUnix)
# Additionally `==` generic for seq[T] has explicit 'noSideEffect' pragma
# so we can check above condition by comparing seq[Time] sequences
let seqA: seq[Time] = @[]
let seqB: seq[Time] = @[]
doAssert seqA == seqB

for tz in [
    (0, "+0", "+00", "+00:00"), # UTC
    (-3600, "+1", "+01", "+01:00"), # CET
    (-39600, "+11", "+11", "+11:00"), # two digits
    (-1800, "+0", "+00", "+00:30"), # half an hour
    (7200, "-2", "-02", "-02:00"), # positive
    (38700, "-10", "-10", "-10:45")]: # positive with three quaters hour
  let ti = DateTime(month: mJan, monthday: 1, utcOffset: tz[0])
  doAssert ti.format("z") == tz[1]
  doAssert ti.format("zz") == tz[2]
  doAssert ti.format("zzz") == tz[3]

block countLeapYears:
  # 1920, 2004 and 2020 are leap years, and should be counted starting at the following year
  doAssert countLeapYears(1920) + 1 == countLeapYears(1921)
  doAssert countLeapYears(2004) + 1 == countLeapYears(2005)
  doAssert countLeapYears(2020) + 1 == countLeapYears(2021)

block timezoneConversion:
  var l = now()
  let u = l.utc
  l = u.local

  doAssert l.timezone == local()
  doAssert u.timezone == utc()

template parseTest(s, f, sExpected: string, ydExpected: int) =
  let
    parsed = s.parse(f, utc())
    parsedStr = $parsed
  check parsedStr == sExpected
  if parsed.yearday != ydExpected:
    echo s
    echo parsed.repr
    echo parsed.yearday, " exp: ", ydExpected
  check(parsed.yearday == ydExpected)

template parseTestTimeOnly(s, f, sExpected: string) =
  check sExpected in $s.parse(f, utc())

# because setting a specific timezone for testing is platform-specific, we use
# explicit timezone offsets in all tests.
template runTimezoneTests() =
  parseTest("Tuesday at 09:04am on Dec 15, 2015 +0",
      "dddd at hh:mmtt on MMM d, yyyy z", "2015-12-15T09:04:00+00:00", 348)
  # ANSIC       = "Mon Jan _2 15:04:05 2006"
  parseTest("Thu Jan 12 15:04:05 2006 +0", "ddd MMM dd HH:mm:ss yyyy z",
      "2006-01-12T15:04:05+00:00", 11)
  # UnixDate    = "Mon Jan _2 15:04:05 MST 2006"
  parseTest("Thu Jan 12 15:04:05 2006 +0", "ddd MMM dd HH:mm:ss yyyy z",
      "2006-01-12T15:04:05+00:00", 11)
  # RubyDate    = "Mon Jan 02 15:04:05 -0700 2006"
  parseTest("Mon Feb 29 15:04:05 -07:00 2016 +0", "ddd MMM dd HH:mm:ss zzz yyyy z",
      "2016-02-29T15:04:05+00:00", 59) # leap day
  # RFC822      = "02 Jan 06 15:04 MST"
  parseTest("12 Jan 16 15:04 +0", "dd MMM yy HH:mm z",
      "2016-01-12T15:04:00+00:00", 11)
  # RFC822Z     = "02 Jan 06 15:04 -0700" # RFC822 with numeric zone
  parseTest("01 Mar 16 15:04 -07:00", "dd MMM yy HH:mm zzz",
      "2016-03-01T22:04:00+00:00", 60) # day after february in leap year
  # RFC850      = "Monday, 02-Jan-06 15:04:05 MST"
  parseTest("Monday, 12-Jan-06 15:04:05 +0", "dddd, dd-MMM-yy HH:mm:ss z",
      "2006-01-12T15:04:05+00:00", 11)
  # RFC1123     = "Mon, 02 Jan 2006 15:04:05 MST"
  parseTest("Sun, 01 Mar 2015 15:04:05 +0", "ddd, dd MMM yyyy HH:mm:ss z",
      "2015-03-01T15:04:05+00:00", 59) # day after february in non-leap year
  # RFC1123Z    = "Mon, 02 Jan 2006 15:04:05 -0700" # RFC1123 with numeric zone
  parseTest("Thu, 12 Jan 2006 15:04:05 -07:00", "ddd, dd MMM yyyy HH:mm:ss zzz",
      "2006-01-12T22:04:05+00:00", 11)
  # RFC3339     = "2006-01-02T15:04:05Z07:00"
  parseTest("2006-01-12T15:04:05Z-07:00", "yyyy-MM-ddTHH:mm:ssZzzz",
      "2006-01-12T22:04:05+00:00", 11)
  parseTest("2006-01-12T15:04:05Z-07:00", "yyyy-MM-dd'T'HH:mm:ss'Z'zzz",
      "2006-01-12T22:04:05+00:00", 11)
  # RFC3339Nano = "2006-01-02T15:04:05.999999999Z07:00"
  parseTest("2006-01-12T15:04:05.999999999Z-07:00",
      "yyyy-MM-ddTHH:mm:ss.999999999Zzzz", "2006-01-12T22:04:05+00:00", 11)
  for tzFormat in ["z", "zz", "zzz"]:
    # formatting timezone as 'Z' for UTC
    parseTest("2001-01-12T22:04:05Z", "yyyy-MM-dd'T'HH:mm:ss" & tzFormat,
        "2001-01-12T22:04:05+00:00", 11)
  # Kitchen     = "3:04PM"
  parseTestTimeOnly("3:04PM", "h:mmtt", "15:04:00")
  #when not defined(testing):
  #  echo "Kitchen: " & $s.parse(f)
  #  var ti = timeToTimeInfo(getTime())
  #  echo "Todays date after decoding: ", ti
  #  var tint = timeToTimeInterval(getTime())
  #  echo "Todays date after decoding to interval: ", tint

  # Bug with parse not setting DST properly if the current local DST differs from
  # the date being parsed. Need to test parse dates both in and out of DST. We
  # are testing that be relying on the fact that tranforming a TimeInfo to a Time
  # and back again will correctly set the DST value. With the incorrect parse
  # behavior this will introduce a one hour offset from the named time and the
  # parsed time if the DST value differs between the current time and the date we
  # are parsing.
  let dstT1 = parse("2016-01-01 00:00:00", "yyyy-MM-dd HH:mm:ss")
  let dstT2 = parse("2016-06-01 00:00:00", "yyyy-MM-dd HH:mm:ss")
  check dstT1 == toTime(dstT1).local
  check dstT2 == toTime(dstT2).local

  block dstTest:
    # parsing will set isDST in relation to the local time. We take a date in
    # January and one in July to maximize the probability to hit one date with DST
    # and one without on the local machine. However, this is not guaranteed.
    let
      parsedJan = parse("2016-01-05 04:00:00+01:00", "yyyy-MM-dd HH:mm:sszzz")
      parsedJul = parse("2016-07-01 04:00:00+01:00", "yyyy-MM-dd HH:mm:sszzz")
    doAssert toTime(parsedJan) == fromUnix(1451962800)
    doAssert toTime(parsedJul) == fromUnix(1467342000)

suite "ttimes":

  # Generate tests for multiple timezone files where available
  # Set the TZ env var for each test
  when defined(Linux) or defined(macosx):
    const tz_dir = "/usr/share/zoneinfo"
    const f = "yyyy-MM-dd HH:mm zzz"
    
    let orig_tz = getEnv("TZ")
    var tz_cnt = 0
    for tz_fn in walkFiles(tz_dir & "/*"):
      if symlinkExists(tz_fn) or tz_fn.endsWith(".tab") or
          tz_fn.endsWith(".list"):
        continue

      test "test for " & tz_fn:
        tz_cnt.inc
        putEnv("TZ", tz_fn)
        runTimezoneTests()

    test "enough timezone files tested":
      check tz_cnt > 10

    test "dst handling":
      putEnv("TZ", "Europe/Stockholm")
      # In case of an impossible time, the time is moved to after the impossible time period
      check initDateTime(26, mMar, 2017, 02, 30, 00).format(f) == "2017-03-26 03:30 +02:00"
      # In case of an ambiguous time, the earlier time is choosen
      check initDateTime(29, mOct, 2017, 02, 00, 00).format(f) == "2017-10-29 02:00 +02:00"
      # These are just dates on either side of the dst switch
      check initDateTime(29, mOct, 2017, 01, 00, 00).format(f) == "2017-10-29 01:00 +02:00"
      check initDateTime(29, mOct, 2017, 01, 00, 00).isDst
      check initDateTime(29, mOct, 2017, 03, 01, 00).format(f) == "2017-10-29 03:01 +01:00"
      check (not initDateTime(29, mOct, 2017, 03, 01, 00).isDst)
      
      check initDateTime(21, mOct, 2017, 01, 00, 00).format(f) == "2017-10-21 01:00 +02:00"

    test "issue #6520":
      putEnv("TZ", "Europe/Stockholm")
      var local = fromUnix(1469275200).local
      var utc = fromUnix(1469275200).utc

      let claimedOffset = local.utcOffset
      local.utcOffset = 0
      check claimedOffset == utc.toTime - local.toTime

    test "issue #5704":
      putEnv("TZ", "Asia/Seoul")
      let diff = parse("19700101-000000", "yyyyMMdd-hhmmss").toTime - parse("19000101-000000", "yyyyMMdd-hhmmss").toTime
      check diff == 2208986872

    test "issue #6465":
      putEnv("TZ", "Europe/Stockholm")      
      let dt = parse("2017-03-25 12:00", "yyyy-MM-dd hh:mm")
      check $(dt + 1.days) == "2017-03-26T12:00:00+02:00"

    test "datetime before epoch":
      check $fromUnix(-2147483648).utc == "1901-12-13T20:45:52+00:00"

    test "adding/subtracting time across dst":
      putenv("TZ", "Europe/Stockholm")

      let dt1 = initDateTime(26, mMar, 2017, 03, 00, 00)
      check $(dt1 - 1.seconds) == "2017-03-26T01:59:59+01:00"

      var dt2 = initDateTime(29, mOct, 2017, 02, 59, 59)
      check  $(dt2 + 1.seconds) == "2017-10-29T02:00:00+01:00"

    putEnv("TZ", orig_tz)

  else:
    # not on Linux or macosx: run one parseTest only
    test "parseTest":
      runTimezoneTests()

  test "isLeapYear":
    check isLeapYear(2016)
    check (not isLeapYear(2015))
    check isLeapYear(2000)
    check (not isLeapYear(1900))

  test "subtract months":
    var dt = initDateTime(1, mFeb, 2017, 00, 00, 00, utc())
    check $(dt - 1.months) == "2017-01-01T00:00:00+00:00"
    dt = initDateTime(15, mMar, 2017, 00, 00, 00, utc())
    check $(dt - 1.months) == "2017-02-15T00:00:00+00:00"
    dt = initDateTime(31, mMar, 2017, 00, 00, 00, utc())
    # This happens due to monthday overflow. It's consistent with Phobos.
    check $(dt - 1.months) == "2017-03-03T00:00:00+00:00"