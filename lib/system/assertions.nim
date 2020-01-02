when not declared(sysFatal):
  include "system/fatal"

# ---------------------------------------------------------------------------
# helpers

type InstantiationInfo = tuple[filename: string, line: int, column: int]

proc `$`(x: int): string {.magic: "IntToStr", noSideEffect.}

proc `$`(info: InstantiationInfo): string =
  # The +1 is needed here
  # instead of overriding `$` (and changing its meaning), consider explicit name.
  info.filename & "(" & $info.line & ", " & $(info.column+1) & ")"

# ---------------------------------------------------------------------------


proc raiseAssert*(msg: string) {.noinline, noreturn.} =
  sysFatal(AssertionError, msg)

proc failedAssertImpl*(msg: string) {.raises: [], tags: [].} =
  # trick the compiler to not list ``AssertionError`` when called
  # by ``assert``.
  type Hide = proc (msg: string) {.noinline, raises: [], noSideEffect,
                                    tags: [].}
  Hide(raiseAssert)(msg)

template assertImpl(cond: bool, msg: string, expr: string, enabled: static[bool]) =
  when enabled:
    const
      loc = instantiationInfo(fullPaths = compileOption("excessiveStackTrace"))
      ploc = $loc
    bind instantiationInfo
    mixin failedAssertImpl
    {.line: loc.}:
      if not cond:
        failedAssertImpl(ploc & " `" & expr & "` " & msg)

template assert*(cond: untyped, msg = "") =
  ## Raises ``AssertionError`` with `msg` if `cond` is false. Note
  ## that ``AssertionError`` is hidden from the effect system, so it doesn't
  ## produce ``{.raises: [AssertionError].}``. This exception is only supposed
  ## to be caught by unit testing frameworks.
  ##
  ## The compiler may not generate any code at all for ``assert`` if it is
  ## advised to do so through the ``-d:danger`` or ``--assertions:off``
  ## `command line switches <nimc.html#compiler-usage-command-line-switches>`_.
  const expr = astToStr(cond)
  assertImpl(cond, msg, expr, compileOption("assertions"))

template doAssert*(cond: untyped, msg = "") =
  ## Similar to ``assert`` but is always turned on regardless of ``--assertions``.
  const expr = astToStr(cond)
  assertImpl(cond, msg, expr, true)

template onFailedAssert*(msg, code: untyped): untyped {.dirty.} =
  ## Sets an assertion failure handler that will intercept any assert
  ## statements following `onFailedAssert` in the current module scope.
  ##
  ## .. code-block:: nim
  ##  # module-wide policy to change the failed assert
  ##  # exception type in order to include a lineinfo
  ##  onFailedAssert(msg):
  ##    var e = new(TMyError)
  ##    e.msg = msg
  ##    e.lineinfo = instantiationInfo(-2)
  ##    raise e
  ##
  template failedAssertImpl(msgIMPL: string): untyped {.dirty.} =
    let msg = msgIMPL
    code

template doAssertRaises*(exception: typedesc, code: untyped) =
  ## Raises ``AssertionError`` if specified ``code`` does not raise the
  ## specified exception. Example:
  ##
  ## .. code-block:: nim
  ##  doAssertRaises(ValueError):
  ##    raise newException(ValueError, "Hello World")
  var wrong = false
  when Exception is exception:
    try:
      if true:
        code
      wrong = true
    except Exception:
      discard
  else:
    try:
      if true:
        code
      wrong = true
    except exception:
      discard
    except Exception:
      raiseAssert(astToStr(exception) &
                  " wasn't raised, another error was raised instead by:\n"&
                  astToStr(code))
  if wrong:
    raiseAssert(astToStr(exception) & " wasn't raised by:\n" & astToStr(code))
