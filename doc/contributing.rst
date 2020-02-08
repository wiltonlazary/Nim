============
Contributing
============

.. contents::


Contributing happens via "Pull requests" (PR) on github. Every PR needs to be
reviewed before it can be merged and the Continuous Integration should be green.

The PR has to be approved (and is often merged too) by one "code owner", either
by the code owner who is responsible for the subsystem the PR belongs to or by
two core developers or by Araq.

See `codeowners <codeowners.html>`_ for more details.


Writing tests
=============

There are 3 types of tests:

1. ``runnableExamples`` documentation comment tests, ran by ``nim doc mymod.nim``
   These end up in documentation and ensure documentation stays in sync with code.

2. tests in ``when isMainModule:`` block, ran by ``nim c mymod.nim``
   ``nimble test`` also typially runs these in external nimble packages.

3. testament tests, e.g.: ``tests/stdlib/tos.nim`` (only used for Nim repo).

Not all the tests follow the convention here, feel free to change the ones
that don't. Always leave the code cleaner than you found it.

Stdlib
------

If you change the stdlib (anything under ``lib/``, e.g. ``lib/pure/os.nim``),
put a test in the file you changed. Add the tests under a ``when isMainModule:``
condition so they only get executed when the tester is building the
file. Each test should be in a separate ``block:`` statement, such that
each has its own scope. Use boolean conditions and ``doAssert`` for the
testing by itself, don't rely on echo statements or similar.

Sample test:

.. code-block:: nim

  when isMainModule:
    block: # newSeqWith tests
      var seq2D = newSeqWith(4, newSeq[bool](2))
      seq2D[0][0] = true
      seq2D[1][0] = true
      seq2D[0][1] = true
      doAssert seq2D == @[@[true, true], @[true, false],
                          @[false, false], @[false, false]]
      # doAssert with `not` can now be done as follows:
      doAssert not (1 == 2)

Newer tests tend to be run via ``testament`` rather than via ``when isMainModule:``,
e.g. ``tests/stdlib/tos.nim``; this allows additional features such as custom
compiler flags; for more details see below.

Compiler
--------

The tests for the compiler use a testing tool called ``testament``. They are all
located in ``tests/`` (e.g.: ``tests/destructor/tdestructor3.nim``).
Each test has its own file. All test files are prefixed with ``t``. If you want
to create a file for import into another test only, use the prefix ``m``.

At the beginning of every test is the expected behavior of the test.
Possible keys are:

- ``cmd``: A compilation command template e.g. ``nim $target --threads:on $options $file``
- ``output``: The expected output (stdout + stderr), most likely via ``echo``
- ``exitcode``: Exit code of the test (via ``exit(number)``)
- ``errormsg``: The expected compiler error message
- ``file``: The file the errormsg was produced at
- ``line``: The line the errormsg was produced at

For a full spec, see here: ``testament/specs.nim``

An example for a test:

.. code-block:: nim

  discard """
    errormsg: "type mismatch: got (PTest)"
  """

  type
    PTest = ref object

  proc test(x: PTest, y: int) = nil

  var buf: PTest
  buf.test()


Running tests
=============

You can run the tests with

::

  ./koch tests

which will run a good subset of tests. Some tests may fail. If you
only want to see the output of failing tests, go for

::

  ./koch tests --failing all

You can also run only a single category of tests. A category is a subdirectory
in the ``tests`` directory. There are a couple of special categories; for a
list of these, see ``testament/categories.nim``, at the bottom.

::

  ./koch tests c lib # compiles/runs stdlib modules, including `isMainModule` tests
  ./koch tests c megatest # runs a set of tests that can be combined into 1

To run a single test:

::

  ./koch test run <category>/<name>    # e.g.: tuples/ttuples_issues
  ./koch test run tests/stdlib/tos.nim # can also provide relative path

For reproducible tests (to reproduce an environment more similar to the one
run by Continuous Integration on travis/appveyor), you may want to disable your
local configuration (e.g. in ``~/.config/nim/nim.cfg``) which may affect some
tests; this can also be achieved by using
``export XDG_CONFIG_HOME=pathtoAlternateConfig`` before running ``./koch``
commands.


Comparing tests
===============

Test failures can be grepped using ``Failure:``.

The tester can compare two test runs. First, you need to create the
reference test. You'll also need to the commit id, because that's what
the tester needs to know in order to compare the two.

::

  git checkout devel
  DEVEL_COMMIT=$(git rev-parse HEAD)
  ./koch tests

Then switch over to your changes and run the tester again.

::

  git checkout your-changes
  ./koch tests

Then you can ask the tester to create a ``testresults.html`` which will
tell you if any new tests passed/failed.

::

  ./koch tests --print html $DEVEL_COMMIT


Deprecation
===========

Backward compatibility is important, so instead of a rename you need to deprecate
the old name and introduce a new name:

.. code-block:: nim

  # for routines (proc/template/macro/iterator) and types:
  proc oldProc(a: int, b: float): bool {.deprecated:
      "deprecated since v1.2.3; use `newImpl: string -> int` instead".} = discard

  # for (const/var/let/fields) the msg is not yet supported:
  const Foo {.deprecated.}  = 1

  # for enum types, you can deprecate the type or some elements
  # (likewise with object types and their fields):
  type Bar {.deprecated.} = enum bar0, bar1
  type Barz  = enum baz0, baz1 {.deprecated.}, baz2


See also `Deprecated <manual.html#pragmas-deprecated-pragma>`_
pragma in the manual.


Documentation
=============

When contributing new procs, be sure to add documentation, especially if
the proc is public. Even private procs benefit from documentation and can be
viewed using ``nim doc --docInternal foo.nim``.
Documentation begins on the line
following the ``proc`` definition, and is prefixed by ``##`` on each line.

Runnable code examples are also encouraged, to show typical behavior with a few
test cases (typically 1 to 3 ``assert`` statements, depending on complexity).
These ``runnableExamples`` are automatically run by ``nim doc mymodule.nim``
as well as ``testament`` and guarantee they stay in sync.

.. code-block:: nim
  proc addBar*(a: string): string =
    ## Adds "Bar" to `a`.
    runnableExamples:
      assert "baz".addBar == "bazBar"
    result = a & "Bar"

See `parentDir <os.html#parentDir,string>`_ example.

The RestructuredText Nim uses has a special syntax for including code snippets
embedded in documentation; these are not run by ``nim doc`` and therefore are
not guaranteed to stay in sync, so ``runnableExamples`` is usually preferred:

.. code-block:: nim

  proc someproc*(): string =
    ## Return "something"
    ##
    ## .. code-block::
    ##  echo someproc() # "something"
    result = "something" # single-hash comments do not produce documentation

The ``.. code-block:: nim`` followed by a newline and an indentation instructs the
``nim doc`` command to produce syntax-highlighted example code with the
documentation (``.. code-block::`` is sufficient from inside a nim module).

When forward declaration is used, the documentation should be included with the
first appearance of the proc.

.. code-block:: nim

  proc hello*(): string
    ## Put documentation here
  proc nothing() = discard
  proc hello*(): string =
    ## ignore this
    echo "hello"

The preferred documentation style is to begin with a capital letter and use
the imperative (command) form. That is, between:

.. code-block:: nim

  proc hello*(): string =
    ## Return "hello"
    result = "hello"

or

.. code-block:: nim

  proc hello*(): string =
    ## says hello
    result = "hello"

the first is preferred.


Best practices
=============

Note: these are general guidelines, not hard rules; there are always exceptions.
Code reviews can just point to a specific section here to save time and
propagate best practices.

.. _define_needs_prefix:
New `defined(foo)` symbols need to be prefixed by the nimble package name, or
by `nim` for symbols in nim sources (e.g. compiler, standard library). This is
to avoid name conflicts across packages.

.. code-block:: nim

  # if in nim sources
  when defined(allocStats): discard # bad, can cause conflicts
  when defined(nimAllocStats): discard # preferred
  # if in a pacakge `cligen`:
  when defined(debug): discard # bad, can cause conflicts
  when defined(cligenDebug): discard # preferred

.. _noimplicitbool:
Take advantage of no implicit bool conversion

.. code-block:: nim

  doAssert isValid() == true
  doAssert isValid() # preferred

.. _design_for_mcs:
Design with method call syntax chaining in mind

.. code-block:: nim

  proc foo(cond: bool, lines: seq[string]) # bad
  proc foo(lines: seq[string], cond: bool) # preferred
  # can be called as: `getLines().foo(false)`

.. _avoid_quit:
Use exceptions (including assert / doAssert) instead of ``quit``
rationale: https://forum.nim-lang.org/t/4089

.. code-block:: nim

  quit() # bad in almost all cases
  doAssert() # preferred

.. _tests_use_doAssert:
Use ``doAssert`` (or ``require``, etc), not ``assert`` in all tests so they'll
be enabled even in release mode (except for tests in ``runnableExamples`` blocks
which for which ``nim doc`` ignores ``-d:release``).

.. code-block:: nim

  when isMainModule:
    assert foo() # bad
    doAssert foo() # preferred

.. _delegate_printing:
Delegate printing to caller: return ``string`` instead of calling ``echo``
rationale: it's more flexible (e.g. allows caller to call custom printing,
including prepending location info, writing to log files, etc).

.. code-block:: nim

  proc foo() = echo "bar" # bad
  proc foo(): string = "bar" # preferred (usually)

.. _use_Option:
[Ongoing debate] Consider using Option instead of return bool + var argument,
unless stack allocation is needed (e.g. for efficiency).

.. code-block:: nim

  proc foo(a: var Bar): bool
  proc foo(): Option[Bar]

.. _use_doAssert_not_echo:
Tests (including in testament) should always prefer assertions over ``echo``,
except when that's not possible. It's more precise, easier for readers and
maintaners to where expected values refer to. See for example
https://github.com/nim-lang/Nim/pull/9335 and https://forum.nim-lang.org/t/4089

.. code-block:: nim

  echo foo() # adds a line for testament in `output:` block inside `discard`.
  doAssert foo() == [1, 2] # preferred, except when not possible to do so.


The Git stuff
=============

General commit rules
--------------------

1. Important, critical bugfixes that have a tiny chance of breaking
   somebody's code should be backported to the latest stable release
   branch (currently 1.0.x). The commit message should contain ``[backport]``
   then.

2. If you introduce changes which affect backwards compatibility,
   make breaking changes, or have PR which is tagged as ``[feature]``,
   the changes should be mentioned in `the changelog
   <https://github.com/nim-lang/Nim/blob/devel/changelog.md>`_.

3. All changes introduced by the commit (diff lines) must be related to the
   subject of the commit.

   If you change something unrelated to the subject parts of the file, because
   your editor reformatted automatically the code or whatever different reason,
   this should be excluded from the commit.

   *Tip:* Never commit everything as is using ``git commit -a``, but review
   carefully your changes with ``git add -p``.

4. Changes should not introduce any trailing whitespace.

   Always check your changes for whitespace errors using ``git diff --check``
   or add following ``pre-commit`` hook:

   .. code-block:: sh

      #!/bin/sh
      git diff --check --cached || exit $?

5. Describe your commit and use your common sense.
   Example commit message:

   ``Fixes #123; refs #124``

   indicates that issue ``#123`` is completely fixed (github may automatically
   close it when the PR is committed), wheres issue ``#124`` is referenced
   (e.g.: partially fixed) and won't close the issue when committed.

6. Commits should be always be rebased against devel (so a fast forward
   merge can happen)

   e.g.: use ``git pull --rebase origin devel``. This is to avoid messing up
   git history.
   Exceptions should be very rare: when rebase gives too many conflicts, simply
   squash all commits using the script shown in
   https://github.com/nim-lang/Nim/pull/9356

7. Do not mix pure formatting changes (e.g. whitespace changes, nimpretty) or
   automated changes (e.g. nimfix) with other code changes: these should be in
   separate commits (and the merge on github should not squash these into 1).


Continuous Integration (CI)
---------------------------

1. Continuous Integration is by default run on every push in a PR; this clogs
   the CI pipeline and affects other PR's; if you don't need it (e.g. for WIP or
   documentation only changes), add ``[ci skip]`` to your commit message title.
   This convention is supported by `Appveyor
   <https://www.appveyor.com/docs/how-to/filtering-commits/#skip-directive-in-commit-message>`_
   and `Travis <https://docs.travis-ci.com/user/customizing-the-build/#skipping-a-build>`_.

2. Consider enabling CI (travis and appveyor) in your own Nim fork, and
   waiting for CI to be green in that fork (fixing bugs as needed) before
   opening your PR in original Nim repo, so as to reduce CI congestion. Same
   applies for updates on a PR: you can test commits on a separate private
   branch before updating the main PR.

Code reviews
------------

1. Whenever possible, use github's new 'Suggested change' in code reviews, which
   saves time explaining the change or applying it; see also
   https://forum.nim-lang.org/t/4317

2. When reviewing large diffs that may involve code moving around, github's interface
   doesn't help much as it doesn't highlight moves. Instead you can use something
   like this, see visual results `here <https://github.com/nim-lang/Nim/pull/10431#issuecomment-456968196>`_:

   .. code-block:: sh

      git fetch origin pull/10431/head && git checkout FETCH_HEAD
      git diff --color-moved-ws=allow-indentation-change --color-moved=blocks HEAD^

3. In addition, you can view github-like diffs locally to identify what was changed
   within a code block using `diff-highlight` or `diff-so-fancy`, e.g.:

   .. code-block:: sh

      # put this in ~/.gitconfig:
      [core]
        pager = "diff-so-fancy | less -R" # or: use: `diff-highlight`



.. include:: docstyle.rst


Evolving the stdlib
===================

As outlined in https://github.com/nim-lang/RFCs/issues/173 there are a couple
of guidelines about what should go into the stdlib, what should be added and
what eventually should be removed.


What the compiler itself needs must be part of the stdlib
---------------------------------------------------------

Maybe in the future the compiler itself can depend on Nimble packages but for
the time being, we strive to have zero dependencies in the compiler as the
compiler is the root of the bootstrapping process and is also used to build
Nimble.


Vocabulary types must be part of the stdlib
-------------------------------------------

These are types most packages need to agree on for better interoperability,
for example ``Option[T]``. This rule also covers the existing collections like
``Table``, ``CountTable`` etc. "Sorted" containers based on a tree-like data
structure are still missing and should be added.

Time handling, especially the ``Time`` type are also covered by this rule.


Existing, battle-tested modules stay
------------------------------------

Reason: There is no benefit in moving them around just to fullfill some design
fashion as in "Nim's core MUST BE SMALL". If you don't like an existing module,
don't import it. If a compilation target (e.g. JS) cannot support a module,
document this limitation.

This covers modules like ``os``, ``osproc``, ``strscans``, ``strutils``,
``strformat``, etc.


Syntactic helpers can start as experimental stdlib modules
----------------------------------------------------------

Reason: Generally speaking as external dependencies they are not exposed
to enough users so that we can see if the shortcuts provide enough benefit
or not. Many programmers avoid external dependencies, even moreso for
"tiny syntactic improvements". However, this is only true for really good
syntactic improvements that have the potential to clean up other parts of
the Nim library substantially. If in doubt, new stdlib modules should start
as external, successful Nimble packages.



Other new stdlib modules do not start as stdlib modules
-------------------------------------------------------

As we strive for higher quality everywhere, it's easier to adopt existing,
battle-tested modules eventually rather than creating modules from scratch.


Little additions are acceptable
-------------------------------

As long as they are documented and tested well, adding little helpers
to existing modules is acceptable. For two reasons:

1. It makes Nim easier to learn and use in the long run.
   ("Why does sequtils lack a ``countIt``?
   Because version 1.0 happens to have lacked it? Silly...")
2. To encourage contributions. Contributors often start with PRs that
   add simple things and then they stay and also fix bugs. Nim is an
   open source project and lives from people's contributions and involvement.
   Newly introduced issues have to be balanced against motivating new people. We know where
   to find perfectly designed pieces of software that have no bugs -- these are the systems
   that nobody uses.
