discard """
  cmd: "nim c --gc:arc $file"
  nimout: '''(a: true, n: doAssert)
Table[system.string, trepr.MyType](data: @[], counter: 0)
nil
'''
"""
import tables

type
  NimSym = distinct NimNode
  MyType = tuple
    a: bool
    n: NimSym

proc myproc(t: MyType) =
  echo repr(t)

proc myproc2(t: MyType) =
  var x = Table[string, t]()
  echo repr(x)

proc myproc3(t: MyType) =
  var x: TableRef[string, t]
  echo repr(x)


macro dumpSym(a: typed) =
  myproc((a: true, n: NimSym(a)))
  myproc2((a: true, n: NimSym(a)))
  myproc3((a: true, n: NimSym(a)))

dumpSym(doAssert)

