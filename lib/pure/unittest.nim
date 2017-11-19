#
#
#            Nim's Runtime Library
#        (c) Copyright 2015 Nim Contributors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## :Author: Zahary Karadjov
##
## This module implements boilerplate to make unit testing easy.
##
## The test status and name is printed after any output or traceback.
##
## Tests can be nested, however failure of a nested test will not mark the
## parent test as failed. Setup and teardown are inherited. Setup can be
## overridden locally.
##
## Compiled test files return the number of failed test as exit code, while
## ``nim c -r <testfile.nim>`` exits with 0 or 1
##
## Running a single test
## ---------------------
##
## Simply specify the test name as a command line argument.
##
## .. code::
##
##   nim c -r test "my super awesome test name"
##
## Example
## -------
##
## .. code:: nim
##
##   suite "description for this stuff":
##     echo "suite setup: run once before the tests"
##
##     setup:
##       echo "run before each test"
##
##     teardown:
##       echo "run after each test"
##
##     test "essential truths":
##       # give up and stop if this fails
##       require(true)
##
##     test "slightly less obvious stuff":
##       # print a nasty message and move on, skipping
##       # the remainder of this block
##       check(1 != 1)
##       check("asd"[2] == 'd')
##
##     test "out of bounds error is thrown on bad access":
##       let v = @[1, 2, 3]  # you can do initialization here
##       expect(IndexError):
##         discard v[4]
##
##     echo "suite teardown: run once after the tests"

import
  macros, strutils, streams, times, sets

when declared(stdout):
  import os

when not defined(ECMAScript):
  import terminal

type
  TestStatus* = enum ## The status of a test when it is done.
    OK,
    FAILED,
    SKIPPED

  OutputLevel* = enum  ## The output verbosity of the tests.
    PRINT_ALL,         ## Print as much as possible.
    PRINT_FAILURES,    ## Print only the failed tests.
    PRINT_NONE         ## Print nothing.

  TestResult* = object
    suiteName*: string
      ## Name of the test suite that contains this test case.
      ## Can be ``nil`` if the test case is not in a suite.
    testName*: string
      ## Name of the test case
    status*: TestStatus

  OutputFormatter* = ref object of RootObj

  ConsoleOutputFormatter* = ref object of OutputFormatter
    colorOutput: bool
      ## Have test results printed in color.
      ## Default is true for the non-js target
      ## unless, the environment variable
      ## ``NIMTEST_NO_COLOR`` is set.
    outputLevel: OutputLevel
      ## Set the verbosity of test results.
      ## Default is ``PRINT_ALL``, unless
      ## the ``NIMTEST_OUTPUT_LVL`` environment
      ## variable is set for the non-js target.
    isInSuite: bool
    isInTest: bool

  JUnitOutputFormatter* = ref object of OutputFormatter
    stream: Stream
    testErrors: seq[string]
    testStartTime: float
    testStackTrace: string

{.deprecated: [TTestStatus: TestStatus, TOutputLevel: OutputLevel]}

var
  abortOnError* {.threadvar.}: bool ## Set to true in order to quit
                                    ## immediately on fail. Default is false,
                                    ## unless the ``NIMTEST_ABORT_ON_ERROR``
                                    ## environment variable is set for
                                    ## the non-js target.

  checkpoints {.threadvar.}: seq[string]
  formatters {.threadvar.}: seq[OutputFormatter]
  testsToRun {.threadvar.}: HashSet[string]

when declared(stdout):
  abortOnError = existsEnv("NIMTEST_ABORT_ON_ERROR")

method suiteStarted*(formatter: OutputFormatter, suiteName: string) {.base, gcsafe.} =
  discard
method testStarted*(formatter: OutputFormatter, testName: string) {.base, gcsafe.} =
  discard
method failureOccurred*(formatter: OutputFormatter, checkpoints: seq[string], stackTrace: string) {.base, gcsafe.} =
  ## ``stackTrace`` is provided only if the failure occurred due to an exception.
  ## ``checkpoints`` is never ``nil``.
  discard
method testEnded*(formatter: OutputFormatter, testResult: TestResult) {.base, gcsafe.} =
  discard
method suiteEnded*(formatter: OutputFormatter) {.base, gcsafe.} =
  discard

proc addOutputFormatter*(formatter: OutputFormatter) =
  if formatters == nil:
    formatters = @[formatter]
  else:
    formatters.add(formatter)

proc newConsoleOutputFormatter*(outputLevel: OutputLevel = PRINT_ALL,
                                colorOutput = true): ConsoleOutputFormatter =
  ConsoleOutputFormatter(
    outputLevel: outputLevel,
    colorOutput: colorOutput
  )

proc defaultConsoleFormatter*(): ConsoleOutputFormatter =
  when declared(stdout):
    # Reading settings
    # On a terminal this branch is executed
    var envOutLvl = os.getEnv("NIMTEST_OUTPUT_LVL").string
    var colorOutput  = not existsEnv("NIMTEST_NO_COLOR")
    var outputLevel = PRINT_ALL
    if envOutLvl.len > 0:
      for opt in countup(low(OutputLevel), high(OutputLevel)):
        if $opt == envOutLvl:
          outputLevel = opt
          break
    result = newConsoleOutputFormatter(outputLevel, colorOutput)
  else:
    result = newConsoleOutputFormatter()

method suiteStarted*(formatter: ConsoleOutputFormatter, suiteName: string) =
  template rawPrint() = echo("\n[Suite] ", suiteName)
  when not defined(ECMAScript):
    if formatter.colorOutput:
      styledEcho styleBright, fgBlue, "\n[Suite] ", resetStyle, suiteName
    else: rawPrint()
  else: rawPrint()
  formatter.isInSuite = true

method testStarted*(formatter: ConsoleOutputFormatter, testName: string) =
  formatter.isInTest = true

method failureOccurred*(formatter: ConsoleOutputFormatter, checkpoints: seq[string], stackTrace: string) =
  if stackTrace != nil:
    echo stackTrace
  let prefix = if formatter.isInSuite: "    " else: ""
  for msg in items(checkpoints):
    echo prefix, msg

method testEnded*(formatter: ConsoleOutputFormatter, testResult: TestResult) =
  formatter.isInTest = false

  if formatter.outputLevel != PRINT_NONE and
     (formatter.outputLevel == PRINT_ALL or testResult.status == FAILED):
    let prefix = if testResult.suiteName != nil: "  " else: ""
    template rawPrint() = echo(prefix, "[", $testResult.status, "] ", testResult.testName)
    when not defined(ECMAScript):
      if formatter.colorOutput and not defined(ECMAScript):
        var color = case testResult.status
                    of OK: fgGreen
                    of FAILED: fgRed
                    of SKIPPED: fgYellow
                    else: fgWhite
        styledEcho styleBright, color, prefix, "[", $testResult.status, "] ", resetStyle, testResult.testName
      else:
        rawPrint()
    else:
      rawPrint()

method suiteEnded*(formatter: ConsoleOutputFormatter) =
  formatter.isInSuite = false

proc xmlEscape(s: string): string =
  result = newStringOfCap(s.len)
  for c in items(s):
    case c:
    of '<': result.add("&lt;")
    of '>': result.add("&gt;")
    of '&': result.add("&amp;")
    of '"': result.add("&quot;")
    of '\'': result.add("&apos;")
    else:
      if ord(c) < 32:
        result.add("&#" & $ord(c) & ';')
      else:
        result.add(c)

proc newJUnitOutputFormatter*(stream: Stream): JUnitOutputFormatter =
  ## Creates a formatter that writes report to the specified stream in
  ## JUnit format.
  ## The ``stream`` is NOT closed automatically when the test are finished,
  ## because the formatter has no way to know when all tests are finished.
  ## You should invoke formatter.close() to finalize the report.
  result = JUnitOutputFormatter(
    stream: stream,
    testErrors: @[],
    testStackTrace: "",
    testStartTime: 0.0
  )
  stream.writeLine("<?xml version=\"1.0\" encoding=\"UTF-8\"?>")
  stream.writeLine("<testsuites>")

proc close*(formatter: JUnitOutputFormatter) =
  ## Completes the report and closes the underlying stream.
  formatter.stream.writeLine("</testsuites>")
  formatter.stream.close()

method suiteStarted*(formatter: JUnitOutputFormatter, suiteName: string) =
  formatter.stream.writeLine("\t<testsuite name=\"$1\">" % xmlEscape(suiteName))

method testStarted*(formatter: JUnitOutputFormatter, testName: string) =
  formatter.testErrors.setLen(0)
  formatter.testStackTrace.setLen(0)
  formatter.testStartTime = epochTime()

method failureOccurred*(formatter: JUnitOutputFormatter, checkpoints: seq[string], stackTrace: string) =
  ## ``stackTrace`` is provided only if the failure occurred due to an exception.
  ## ``checkpoints`` is never ``nil``.
  formatter.testErrors.add(checkpoints)
  if stackTrace != nil:
    formatter.testStackTrace = stackTrace

method testEnded*(formatter: JUnitOutputFormatter, testResult: TestResult) =
  let time = epochTime() - formatter.testStartTime
  let timeStr = time.formatFloat(ffDecimal, precision = 8)
  formatter.stream.writeLine("\t\t<testcase name=\"$#\" time=\"$#\">" % [xmlEscape(testResult.testName), timeStr])
  case testResult.status:
  of OK:
    discard
  of SKIPPED:
    formatter.stream.writeLine("<skipped />")
  of FAILED:
    let failureMsg = if formatter.testStackTrace.len > 0 and
                        formatter.testErrors.len > 0:
                       xmlEscape(formatter.testErrors[^1])
                     elif formatter.testErrors.len > 0:
                       xmlEscape(formatter.testErrors[0])
                     else: "The test failed without outputting an error"

    var errs = ""
    if formatter.testErrors.len > 1:
      var startIdx = if formatter.testStackTrace.len > 0: 0 else: 1
      var endIdx = if formatter.testStackTrace.len > 0: formatter.testErrors.len - 2
                   else: formatter.testErrors.len - 1

      for errIdx in startIdx..endIdx:
        if errs.len > 0:
          errs.add("\n")
        errs.add(xmlEscape(formatter.testErrors[errIdx]))

    if formatter.testStackTrace.len > 0:
      formatter.stream.writeLine("\t\t\t<error message=\"$#\">$#</error>" % [failureMsg, xmlEscape(formatter.testStackTrace)])
      if errs.len > 0:
        formatter.stream.writeLine("\t\t\t<system-err>$#</system-err>" % errs)
    else:
      formatter.stream.writeLine("\t\t\t<failure message=\"$#\">$#</failure>" % [failureMsg, errs])

  formatter.stream.writeLine("\t\t</testcase>")

method suiteEnded*(formatter: JUnitOutputFormatter) =
  formatter.stream.writeLine("\t</testsuite>")

proc shouldRun(testName: string): bool =
  if testsToRun.len == 0:
    return true

  result = testName in testsToRun

proc ensureInitialized() =
  if formatters == nil:
    formatters = @[OutputFormatter(defaultConsoleFormatter())]

  if not testsToRun.isValid:
    testsToRun.init()
    when declared(paramCount):
      # Read tests to run from the command line.
      for i in 1 .. paramCount():
        testsToRun.incl(paramStr(i))

# These two procs are added as workarounds for
# https://github.com/nim-lang/Nim/issues/5549
proc suiteEnded() =
  for formatter in formatters:
    formatter.suiteEnded()

proc testEnded(testResult: TestResult) =
  for formatter in formatters:
    formatter.testEnded(testResult)

template suite*(name, body) {.dirty.} =
  ## Declare a test suite identified by `name` with optional ``setup``
  ## and/or ``teardown`` section.
  ##
  ## A test suite is a series of one or more related tests sharing a
  ## common fixture (``setup``, ``teardown``). The fixture is executed
  ## for EACH test.
  ##
  ## .. code-block:: nim
  ##  suite "test suite for addition":
  ##    setup:
  ##      let result = 4
  ##
  ##    test "2 + 2 = 4":
  ##      check(2+2 == result)
  ##
  ##    test "(2 + -2) != 4":
  ##      check(2 + -2 != result)
  ##
  ##    # No teardown needed
  ##
  ## The suite will run the individual test cases in the order in which
  ## they were listed. With default global settings the above code prints:
  ##
  ## .. code-block::
  ##
  ##  [Suite] test suite for addition
  ##    [OK] 2 + 2 = 4
  ##    [OK] (2 + -2) != 4
  bind formatters, ensureInitialized, suiteEnded

  block:
    template setup(setupBody: untyped) {.dirty, used.} =
      var testSetupIMPLFlag {.used.} = true
      template testSetupIMPL: untyped {.dirty.} = setupBody

    template teardown(teardownBody: untyped) {.dirty, used.} =
      var testTeardownIMPLFlag {.used.} = true
      template testTeardownIMPL: untyped {.dirty.} = teardownBody

    let testSuiteName {.used.} = name

    ensureInitialized()
    try:
      for formatter in formatters:
        formatter.suiteStarted(name)
      body
    finally:
      suiteEnded()

template test*(name, body) {.dirty.} =
  ## Define a single test case identified by `name`.
  ##
  ## .. code-block:: nim
  ##
  ##  test "roses are red":
  ##    let roses = "red"
  ##    check(roses == "red")
  ##
  ## The above code outputs:
  ##
  ## .. code-block::
  ##
  ##  [OK] roses are red
  bind shouldRun, checkpoints, formatters, ensureInitialized, testEnded

  ensureInitialized()

  if shouldRun(name):
    checkpoints = @[]
    var testStatusIMPL {.inject.} = OK

    for formatter in formatters:
      formatter.testStarted(name)

    try:
      when declared(testSetupIMPLFlag): testSetupIMPL()
      when declared(testTeardownIMPLFlag):
        defer: testTeardownIMPL()
      body

    except:
      when not defined(js):
        checkpoint("Unhandled exception: " & getCurrentExceptionMsg())
        var stackTrace {.inject.} = getCurrentException().getStackTrace()
      fail()

    finally:
      if testStatusIMPL == FAILED:
        programResult += 1
      let testResult = TestResult(
        suiteName: when declared(testSuiteName): testSuiteName else: nil,
        testName: name,
        status: testStatusIMPL
      )
      testEnded(testResult)
      checkpoints = @[]

proc checkpoint*(msg: string) =
  ## Set a checkpoint identified by `msg`. Upon test failure all
  ## checkpoints encountered so far are printed out. Example:
  ##
  ## .. code-block:: nim
  ##
  ##  checkpoint("Checkpoint A")
  ##  check((42, "the Answer to life and everything") == (1, "a"))
  ##  checkpoint("Checkpoint B")
  ##
  ## outputs "Checkpoint A" once it fails.
  if checkpoints == nil:
    checkpoints = @[]
  checkpoints.add(msg)
  # TODO: add support for something like SCOPED_TRACE from Google Test

template fail* =
  ## Print out the checkpoints encountered so far and quit if ``abortOnError``
  ## is true. Otherwise, erase the checkpoints and indicate the test has
  ## failed (change exit code and test status). This template is useful
  ## for debugging, but is otherwise mostly used internally. Example:
  ##
  ## .. code-block:: nim
  ##
  ##  checkpoint("Checkpoint A")
  ##  complicatedProcInThread()
  ##  fail()
  ##
  ## outputs "Checkpoint A" before quitting.
  bind ensureInitialized

  when declared(testStatusIMPL):
    testStatusIMPL = FAILED
  else:
    programResult += 1

  ensureInitialized()

    # var stackTrace: string = nil
  for formatter in formatters:
    when declared(stackTrace):
      formatter.failureOccurred(checkpoints, stackTrace)
    else:
      formatter.failureOccurred(checkpoints, nil)

  when not defined(ECMAScript):
    if abortOnError: quit(programResult)

  checkpoints = @[]

template skip* =
  ## Mark the test as skipped. Should be used directly
  ## in case when it is not possible to perform test
  ## for reasons depending on outer environment,
  ## or certain application logic conditions or configurations.
  ## The test code is still executed.
  ##
  ## .. code-block:: nim
  ##
  ##  if not isGLConextCreated():
  ##    skip()
  bind checkpoints

  testStatusIMPL = SKIPPED
  checkpoints = @[]

macro check*(conditions: untyped): untyped =
  ## Verify if a statement or a list of statements is true.
  ## A helpful error message and set checkpoints are printed out on
  ## failure (if ``outputLevel`` is not ``PRINT_NONE``).
  ## Example:
  ##
  ## .. code-block:: nim
  ##
  ##  import strutils
  ##
  ##  check("AKB48".toLowerAscii() == "akb48")
  ##
  ##  let teams = {'A', 'K', 'B', '4', '8'}
  ##
  ##  check:
  ##    "AKB48".toLowerAscii() == "akb48"
  ##    'C' in teams
  let checked = callsite()[1]

  template asgn(a: untyped, value: typed) =
    var a = value # XXX: we need "var: var" here in order to
                  # preserve the semantics of var params

  template print(name: untyped, value: typed) =
    when compiles(string($value)):
      checkpoint(name & " was " & $value)

  proc inspectArgs(exp: NimNode): tuple[assigns, check, printOuts: NimNode] =
    result.check = copyNimTree(exp)
    result.assigns = newNimNode(nnkStmtList)
    result.printOuts = newNimNode(nnkStmtList)

    var counter = 0

    if exp[0].kind == nnkIdent and
        $exp[0] in ["not", "in", "notin", "==", "<=",
                    ">=", "<", ">", "!=", "is", "isnot"]:

      for i in 1 ..< exp.len:
        if exp[i].kind notin nnkLiterals:
          inc counter
          let argStr = exp[i].toStrLit
          let paramAst = exp[i]
          if exp[i].kind == nnkIdent:
            result.printOuts.add getAst(print(argStr, paramAst))
          if exp[i].kind in nnkCallKinds + { nnkDotExpr, nnkBracketExpr }:
            let callVar = newIdentNode(":c" & $counter)
            result.assigns.add getAst(asgn(callVar, paramAst))
            result.check[i] = callVar
            result.printOuts.add getAst(print(argStr, callVar))
          if exp[i].kind == nnkExprEqExpr:
            # ExprEqExpr
            #   Ident !"v"
            #   IntLit 2
            result.check[i] = exp[i][1]
          if exp[i].typekind notin {ntyTypeDesc}:
            let arg = newIdentNode(":p" & $counter)
            result.assigns.add getAst(asgn(arg, paramAst))
            result.printOuts.add getAst(print(argStr, arg))
            if exp[i].kind != nnkExprEqExpr:
              result.check[i] = arg
            else:
              result.check[i][1] = arg

  case checked.kind
  of nnkCallKinds:

    let (assigns, check, printOuts) = inspectArgs(checked)
    let lineinfo = newStrLitNode(checked.lineinfo)
    let callLit = checked.toStrLit
    result = quote do:
      block:
        `assigns`
        if not `check`:
          checkpoint(`lineinfo` & ": Check failed: " & `callLit`)
          `printOuts`
          fail()

  of nnkStmtList:
    result = newNimNode(nnkStmtList)
    for node in checked:
      if node.kind != nnkCommentStmt:
        result.add(newCall(!"check", node))

  else:
    let lineinfo = newStrLitNode(checked.lineinfo)
    let callLit = checked.toStrLit

    result = quote do:
      if not `checked`:
        checkpoint(`lineinfo` & ": Check failed: " & `callLit`)
        fail()

template require*(conditions: untyped) =
  ## Same as `check` except any failed test causes the program to quit
  ## immediately. Any teardown statements are not executed and the failed
  ## test output is not generated.
  let savedAbortOnError = abortOnError
  block:
    abortOnError = true
    check conditions
  abortOnError = savedAbortOnError

macro expect*(exceptions: varargs[typed], body: untyped): untyped =
  ## Test if `body` raises an exception found in the passed `exceptions`.
  ## The test passes if the raised exception is part of the acceptable
  ## exceptions. Otherwise, it fails.
  ## Example:
  ##
  ## .. code-block:: nim
  ##
  ##  import math, random
  ##  proc defectiveRobot() =
  ##    randomize()
  ##    case random(1..4)
  ##    of 1: raise newException(OSError, "CANNOT COMPUTE!")
  ##    of 2: discard parseInt("Hello World!")
  ##    of 3: raise newException(IOError, "I can't do that Dave.")
  ##    else: assert 2 + 2 == 5
  ##
  ##  expect IOError, OSError, ValueError, AssertionError:
  ##    defectiveRobot()
  let exp = callsite()
  template expectBody(errorTypes, lineInfoLit, body): NimNode {.dirty.} =
    try:
      body
      checkpoint(lineInfoLit & ": Expect Failed, no exception was thrown.")
      fail()
    except errorTypes:
      discard
    except:
      checkpoint(lineInfoLit & ": Expect Failed, unexpected exception was thrown.")
      fail()

  var body = exp[exp.len - 1]

  var errorTypes = newNimNode(nnkBracket)
  for i in countup(1, exp.len - 2):
    errorTypes.add(exp[i])

  result = getAst(expectBody(errorTypes, exp.lineinfo, body))
