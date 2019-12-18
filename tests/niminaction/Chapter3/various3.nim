discard """
output: '''
Future is no longer empty, 42
'''
"""

import threadpool
proc foo: string = "Dog"
var x: FlowVar[string] = spawn foo()
assert(^x == "Dog")

block:
  type
    Box = object
      case empty: bool
      of false:
        contents: string
      else:
        discard

  var obj = Box(empty: false, contents: "Hello")
  assert obj.contents == "Hello"

  var obj2 = Box(empty: true)
  doAssertRaises(FieldError):
    echo(obj2.contents)

import json
assert parseJson("null").kind == JNull
assert parseJson("true").kind == JBool
assert parseJson("42").kind == JInt
assert parseJson("3.14").kind == JFloat
assert parseJson("\"Hi\"").kind == JString
assert parseJson("""{ "key": "value" }""").kind == JObject
assert parseJson("[1, 2, 3, 4]").kind == JArray

import json
let data = """
  {"username": "Dominik"}
"""

let obj = parseJson(data)
assert obj.kind == JObject
assert obj["username"].kind == JString
assert obj["username"].str == "Dominik"

block:
  proc count10(): int =
    for i in 0 ..< 10:
      result.inc
  assert count10() == 10

type
  Point = tuple[x, y: int]

var point = (5, 10)
var point2 = (x: 5, y: 10)

type
  Human = object
    name: string
    age: int

var jeff = Human(name: "Jeff", age: 23)
var amy = Human(name: "Amy", age: 20)

import asyncdispatch

var future = newFuture[int]()
doAssert(not future.finished)

future.callback =
  proc (future: Future[int]) =
    echo("Future is no longer empty, ", future.read)

future.complete(42)

import asyncdispatch, asyncfile

when false:
  var file = openAsync("")
  let dataFut = file.readAll()
  dataFut.callback =
    proc (future: Future[string]) =
      echo(future.read())

  asyncdispatch.runForever()

import asyncdispatch, asyncfile, os

proc readFiles() {.async.} =
  # --- Changed to getTempDir here.
  var file = openAsync(getTempDir() / "test.txt", fmReadWrite)
  let data = await file.readAll()
  echo(data)
  await file.write("Hello!\n")

waitFor readFiles()
