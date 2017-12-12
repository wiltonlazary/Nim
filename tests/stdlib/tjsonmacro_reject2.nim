discard """
  file: "tjsonmacro_reject2.nim"
  line: 10
  errormsg: "The `to` macro does not support ref objects with cycles."
"""
import json

type
  Misdirection = object
    cycle: Cycle

  Cycle = ref object
    foo: string
    cycle: Misdirection

let data = """
  {"cycle": null}
"""

let dataParsed = parseJson(data)
let dataDeser = to(dataParsed, Cycle)