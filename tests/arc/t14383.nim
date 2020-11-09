discard """
  cmd: "nim c --gc:arc $file"
  output: '''
hello
hello
@["a", "b"]
'''
"""

import dmodule

var val = parseMinValue()
if val.kind == minDictionary:
  echo val

#------------------------------------------------------------------------------
# Issue #15238
#------------------------------------------------------------------------------

proc sinkArg(x: sink seq[string]) =
  discard

proc varArg(lst: var seq[string]) = 
  sinkArg(lst)

var x = @["a", "b"]
varArg(x)
echo x


#------------------------------------------------------------------------------
# Issue #15286
#------------------------------------------------------------------------------

import std/os
discard getFileInfo(".")


#------------------------------------------------------------------------------
# Issue #15707
#------------------------------------------------------------------------------

type
  JVMObject = ref object
proc freeJVMObject(o: JVMObject) =
  discard
proc fromJObject(T: typedesc[JVMObject]): T =
  result.new(cast[proc(r: T) {.nimcall.}](freeJVMObject))

discard JVMObject.fromJObject()