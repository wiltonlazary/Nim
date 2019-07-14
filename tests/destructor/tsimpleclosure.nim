discard """
  cmd: '''nim c --newruntime $file'''
  output: '''a b
70
hello
hello
hello
2 2  alloc/dealloc pairs: 0'''
"""

import core / allocators
import system / ansi_c

proc main(): owned(proc()) =
  var a = "a"
  var b = "b"
  result = proc() =
    echo a, " ", b


proc foo(f: (iterator(): int)) =
  for i in f(): echo i

proc wrap =
  let p = main()
  p()

  let fIt = iterator(): int = yield 70
  foo fIt

wrap()

# bug #11533
proc say = echo "hello"

# Error: internal error: genAssignment: tyNil
var err0: proc() = say
err0()

var ok0: proc()
ok0 = say
ok0()

var ok1 = say
ok1()

let (a, d) = allocCounters()
discard cprintf("%ld %ld  alloc/dealloc pairs: %ld\n", a, d, system.allocs)
