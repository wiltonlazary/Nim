discard """
  errormsg: "cannot instantiate B"
  line: 20
  nimout: '''
got: <type string>
but expected: <T: A>
'''
"""

type
  A = concept c
    advance(c)

  B[T: A] = object
    child: ref B[T]

proc advance(x: int): int = x + 1

var a: B[int]
var b: B[string]

