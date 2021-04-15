# v1.6.x - yyyy-mm-dd



## Changes affecting backward compatibility

- `repr` now doesn't insert trailing newline; previous behavior was very inconsistent,
  see #16034. Use `-d:nimLegacyReprWithNewline` for previous behavior.

- An enum now can't be converted to another enum directly, you must use `ord` (or `cast`, but
  compiler won't help if you misuse it).
  ```
  type A = enum a1, a2
  type B = enum b1, b2
  doAssert not compiles(a1.B)
  doAssert compiles(a1.ord.B)
  ```
  for a transition period, use `-d:nimLegacyConvEnumEnum`.

- Type mismatch errors now show more context, use `-d:nimLegacyTypeMismatch` for previous
  behavior.

- `echo` and `debugEcho` will now raise `IOError` if writing to stdout fails.  Previous behavior
  silently ignored errors.  See #16366.  Use `-d:nimLegacyEchoNoRaise` for previous behavior.

- `math.round` now is rounded "away from zero" in JS backend which is consistent
  with other backends. See #9125. Use `-d:nimLegacyJsRound` for previous behavior.

- Changed the behavior of `uri.decodeQuery` when there are unencoded `=`
  characters in the decoded values. Prior versions would raise an error. This is
  no longer the case to comply with the HTML spec and other languages
  implementations. Old behavior can be obtained with
  `-d:nimLegacyParseQueryStrict`. `cgi.decodeData` which uses the same
  underlying code is also updated the same way.
- Custom pragma values have now an API for use in macros.

- In `std/os`, `getHomeDir`, `expandTilde`, `getTempDir`, `getConfigDir` now do not include trailing `DirSep`,
  unless `-d:nimLegacyHomeDir` is specified (for a transition period).

## Standard library additions and changes

- Added `sections` iterator in `parsecfg`.

- Make custom op in macros.quote work for all statements.

- On Windows the SSL library now checks for valid certificates.
  It uses the `cacert.pem` file for this purpose which was extracted
  from `https://curl.se/ca/cacert.pem`. Besides
  the OpenSSL DLLs (e.g. libssl-1_1-x64.dll, libcrypto-1_1-x64.dll) you
  now also need to ship `cacert.pem` with your `.exe` file.


- Make `{.requiresInit.}` pragma to work for `distinct` types.

- Added a macros `enumLen` for returning the number of items in an enum to the
  `typetraits.nim` module.

- `prelude` now works with the JavaScript target.
  Added `sequtils` import to `prelude`.
  `prelude` can now be used via `include std/prelude`, but `include prelude` still works.

- Added `almostEqual` in `math` for comparing two float values using a machine epsilon.

- Added `clamp` in `math` which allows using a `Slice` to clamp to a value.

- The JSON module can now handle integer literals and floating point literals of
  arbitrary length and precision.
  Numbers that do not fit the underlying `BiggestInt` or `BiggestFloat` fields are
  kept as string literals and one can use external BigNum libraries to handle these.
  The `parseFloat` family of functions also has now optional `rawIntegers` and
  `rawFloats` parameters that can be used to enforce that all integer or float
  literals remain in the "raw" string form so that client code can easily treat
  small and large numbers uniformly.

- Added `BackwardsIndex` overload for `JsonNode`.

- added `jsonutils.jsonTo` overload with `opt = Joptions()` param.

- `json.%`,`json.to`, `jsonutils.formJson`,`jsonutils.toJson` now work with `uint|uint64`
  instead of raising (as in 1.4) or giving wrong results (as in 1.2).

- Added an overload for the `collect` macro that inferes the container type based
  on the syntax of the last expression. Works with std seqs, tables and sets.

- `jsonutils` now handles `cstring` (including as Table key).

- Added `randState` template that exposes the default random number generator.
  Useful for library authors.

- Added `std/enumutils` module. Added `genEnumCaseStmt` macro that generates case statement to parse string to enum.
  Added `items` for enums with holes.
  Added `symbolName` to return the enum symbol name ignoring the human readable name.

- Added `typetraits.HoleyEnum` for enums with holes, `OrdinalEnum` for enums without holes.

- Removed deprecated `iup` module from stdlib, it has already moved to
  [nimble](https://github.com/nim-lang/iup).

- various functions in `httpclient` now accept `url` of type `Uri`. Moreover `request` function's
  `httpMethod` argument of type `string` was deprecated in favor of `HttpMethod` enum type.

- `nodejs` backend now supports osenv: `getEnv`, `putEnv`, `envPairs`, `delEnv`, `existsEnv`.

- Added `cmpMem` to `system`.

- `doAssertRaises` now correctly handles foreign exceptions.

- Added `asyncdispatch.activeDescriptors` that returns the number of currently
  active async event handles/file descriptors.

- Added `getPort` to `asynchttpserver`.

- `--gc:orc` is now 10% faster than previously for common workloads. If
  you have trouble with its changed behavior, compile with `-d:nimOldOrc`.


- `os.FileInfo` (returned by `getFileInfo`) now contains `blockSize`,
  determining preferred I/O block size for this file object.

- Added a simpler to use `io.readChars` overload.

- Added `**` to jsffi.

- `writeStackTrace` is available in JS backend now.

- Added `decodeQuery` to `std/uri`.

- `strscans.scanf` now supports parsing single characters.

- `strscans.scanTuple` added which uses `strscans.scanf` internally,
  returning a tuple which can be unpacked for easier usage of `scanf`.

- Added `setutils.toSet` that can take any iterable and convert it to a built-in `set`,
  if the iterable yields a built-in settable type.

- Added `setutils.fullSet` which returns a full built-in `set` for a valid type.

- Added `setutils.complement` which returns the complement of a built-in `set`.

- Added `setutils.[]=`.

- Added `math.isNaN`.

- Added `jsbigints` module, arbitrary precision integers for JavaScript target.

- Added `math.copySign`.

- Added new operations for singly- and doubly linked lists: `lists.toSinglyLinkedList`
  and `lists.toDoublyLinkedList` convert from `openArray`s; `lists.copy` implements
  shallow copying; `lists.add` concatenates two lists - an O(1) variation that consumes
  its argument, `addMoved`, is also supplied.

- Added `euclDiv` and `euclMod` to `math`.

- Added `httpcore.is1xx` and missing HTTP codes.

- Added `jsconsole.jsAssert` for JavaScript target.

- Added `posix_utils.osReleaseFile` to get system identification from `os-release` file on Linux and the BSDs.
  https://www.freedesktop.org/software/systemd/man/os-release.html

- Added `socketstream` module that wraps sockets in the stream interface

- Added `sugar.dumpToString` which improves on `sugar.dump`.

- Added `math.signbit`.

- Removed the optional `longestMatch` parameter of the `critbits._WithPrefix` iterators (it never worked reliably)

- In `lists`: renamed `append` to `add` and retained `append` as an alias;
  added `prepend` and `prependMoved` analogously to `add` and `addMoved`;
  added `remove` for `SinglyLinkedList`s.

- Deprecated `any`. See https://github.com/nim-lang/RFCs/issues/281

- Added `std/sysrand` module to get random numbers from a secure source
  provided by the operating system.

- Added optional `options` argument to `copyFile`, `copyFileToDir`, and
  `copyFileWithPermissions`. By default, on non-Windows OSes, symlinks are
  followed (copy files symlinks point to); on Windows, `options` argument is
  ignored and symlinks are skipped.

- On non-Windows OSes, `copyDir` and `copyDirWithPermissions` copy symlinks as
  symlinks (instead of skipping them as it was before); on Windows symlinks are
  skipped.

- On non-Windows OSes, `moveFile` and `moveDir` move symlinks as symlinks
  (instead of skipping them sometimes as it was before).

- Added optional `followSymlinks` argument to `setFilePermissions`.

- Added `os.isAdmin` to tell whether the caller's process is a member of the
  Administrators local group (on Windows) or a root (on POSIX).

- Added `random.initRand()` overload with no argument which uses the current time as a seed.

- Added experimental `linenoise.readLineStatus` to get line and status (e.g. ctrl-D or ctrl-C).

- Added `compilesettings.SingleValueSetting.libPath`.

- `std/wrapnils` doesn't use `experimental:dotOperators` anymore, avoiding
  issues like https://github.com/nim-lang/Nim/issues/13063 (which affected error messages)
  for modules importing `std/wrapnils`.
  Added `??.` macro which returns an `Option`.

- Added `math.frexp` overload procs. Deprecated `c_frexp`, use `frexp` instead.

- `parseopt.initOptParser` has been made available and `parseopt` has been
  added back to `prelude` for all backends. Previously `initOptParser` was
  unavailable if the `os` module did not have `paramCount` or `paramStr`,
  but the use of these in `initOptParser` were conditionally to the runtime
  arguments passed to it, so `initOptParser` has been changed to raise
  `ValueError` when the real command line is not available. `parseopt` was
  previously excluded from `prelude` for JS, as it could not be imported.

- On POSIX systems, the default signal handlers used for Nim programs (it's
  used for printing the stacktrace on fatal signals) will now re-raise the
  signal for the OS default handlers to handle.

  This lets the OS perform its default actions, which might include core
  dumping (on select signals) and notifying the parent process about the cause
  of termination.

- Added `system.prepareStrMutation` for better support of low
  level `moveMem`, `copyMem` operations for Orc's copy-on-write string
  implementation.

- `hashes.hash` now supports `object`, but can be overloaded.

- Added `std/strbasics` for high performance string operations.
  Added `strip`, `setSlice`, `add(a: var string, b: openArray[char])`.

- `hashes.hash` now supports `object`, but can be overloaded.

- Added to `wrapnils` an option-like API via `??.`, `isSome`, `get`.

- `std/options` changed `$some(3)` to `"some(3)"` instead of `"Some(3)"`
  and `$none(int)` to `"none(int)"` instead of `"None[int]"`.

- Added `algorithm.merge`.


- Added `std/jsfetch` module [Fetch](https://developer.mozilla.org/docs/Web/API/Fetch_API) wrapper for JavaScript target.

- Added `std/jsheaders` module [Headers](https://developer.mozilla.org/en-US/docs/Web/API/Headers) wrapper for JavaScript target.

- Added `std/jsformdata` module [FormData](https://developer.mozilla.org/en-US/docs/Web/API/FormData) wrapper for JavaScript target.

- `system.addEscapedChar` now renders `\r` as `\r` instead of `\c`, to be compatible
  with most other languages.

- Removed support for named procs in `sugar.=>`.

- Added `jscore.debugger` to [call any available debugging functionality, such as breakpoints.](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Statements/debugger).

- Added `std/channels`.

- Added `htmlgen.portal` for [making "SPA style" pages using HTML only](https://web.dev/hands-on-portals).

- Added `ZZZ` and `ZZZZ` patterns to `times.nim` `DateTime` parsing, to match time
  zone offsets without colons, e.g. `UTC+7 -> +0700`.

- Added `jsconsole.dir`, `jsconsole.dirxml`, `jsconsole.timeStamp`.

- Added dollar `$` and `len` for `jsre.RegExp`.

- Added `std/tasks`.

- Added `hasDataBuffered` to `asyncnet`.

- Added `hasClosure` to `std/typetraits`.

- Added `genasts.genAst` that avoids the problems inherent with `quote do` and can
  be used as a replacement.

## Language changes

- `nimscript` now handles `except Exception as e`.

- The `cstring` doesn't support `[]=` operator in JS backend.

- nil dereference is not allowed at compile time. `cast[ptr int](nil)[]` is rejected at compile time.

- `typetraits.distinctBase` now is identity instead of error for non distinct types.

- `os.copyFile` is now 2.5x faster on OSX, by using `copyfile` from `copyfile.h`;
  use `-d:nimLegacyCopyFile` for OSX < 10.5.

- The required name of case statement macros for the experimental
  `caseStmtMacros` feature has changed from `match` to `` `case` ``.

- `typedesc[Foo]` now renders as such instead of `type Foo` in compiler messages.

- The unary minus in `-1` is now part of the integer literal, it is now parsed as a single token.
  This implies that edge cases like `-128'i8` finally work correctly.

- Custom numeric literals (e.g. `-128'bignum`) are now supported.

- Tuple expressions are now parsed consistently as
  `nnkTupleConstr` node. Will affect macros expecting nodes to be of `nnkPar`.

- `nim e` now accepts arbitrary file extensions for the nimscript file,
  although `.nims` is still the preferred extension in general.

- Added `iterable[T]` type class to match called iterators, which enables writing:
  `template fn(a: iterable)` instead of `template fn(a: untyped)`


## Compiler changes

- Added `--declaredlocs` to show symbol declaration location in messages.

- Deprecated `TaintedString` and `--taintmode`.

- Deprecated `--nilseqs` which is now a noop.

- Added `--spellSuggest` to show spelling suggestions on typos.

- Source+Edit links now appear on top of every docgen'd page when
  `nim doc --git.url:url ...` is given.

- Added `nim --eval:cmd` to evaluate a command directly, see `nim --help`.

- VM now supports `addr(mystring[ind])` (index + index assignment)

- Added `--hintAsError` with similar semantics as `--warningAsError`.

- TLS: OSX now uses native TLS (`--tlsEmulation:off`), TLS now works with importcpp non-POD types,
  such types must use `.cppNonPod` and `--tlsEmulation:off`should be used.

- Now array literals(JS backend) uses JS typed arrays when the corresponding js typed array exists, for example `[byte(1), 2, 3]` generates `new Uint8Array([1, 2, 3])`.

- docgen: rst files can now use single backticks instead of double backticks and correctly render
  in both rst2html (as before) as well as common tools rendering rst directly (e.g. github), by
  adding: `default-role:: code` directive inside the rst file, which is now handled by rst2html.

- Added `-d:nimStrictMode` in CI in several places to ensure code doesn't have certain hints/warnings

- Added `then`, `catch` to `asyncjs`, for now hidden behind `-d:nimExperimentalAsyncjsThen`.

- `--newruntime` and `--refchecks` are deprecated.

- Added `unsafeIsolate` and `extract` to `std/isolation`.

- `--hint:CC` now goes to stderr (like all other hints) instead of stdout.



## Tool changes

- The rst parser now supports markdown table syntax.
  Known limitations:
  - cell alignment is not supported, i.e. alignment annotations in a delimiter
    row (`:---`, `:--:`, `---:`) are ignored,
  - every table row must start with `|`, e.g. `| cell 1 | cell 2 |`.

- `fusion` is now un-bundled from nim, `./koch fusion` will
  install it via nimble at a fixed hash.
