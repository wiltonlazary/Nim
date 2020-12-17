#
#
#            Nim's Runtime Library
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## *Constructive mathematics is naturally typed.* -- Simon Thompson
##
## Basic math routines for Nim.
##
## Note that the trigonometric functions naturally operate on radians.
## The helper functions `degToRad<#degToRad,T>`_ and `radToDeg<#radToDeg,T>`_
## provide conversion between radians and degrees.
##
## .. code-block::
##
##   import math
##   from sequtils import map
##
##   let a = [0.0, PI/6, PI/4, PI/3, PI/2]
##
##   echo a.map(sin)
##   # @[0.0, 0.499…, 0.707…, 0.866…, 1.0]
##
##   echo a.map(tan)
##   # @[0.0, 0.577…, 0.999…, 1.732…, 1.633…e+16]
##
##   echo cos(degToRad(180.0))
##   # -1.0
##
##   echo sqrt(-1.0)
##   # nan   (use `complex` module)
##
## This module is available for the `JavaScript target
## <backends.html#backends-the-javascript-target>`_.
##
## **See also:**
## * `complex module<complex.html>`_ for complex numbers and their
##   mathematical operations
## * `rationals module<rationals.html>`_ for rational numbers and their
##   mathematical operations
## * `fenv module<fenv.html>`_ for handling of floating-point rounding
##   and exceptions (overflow, zero-divide, etc.)
## * `random module<random.html>`_ for fast and tiny random number generator
## * `mersenne module<mersenne.html>`_ for Mersenne twister random number generator
## * `stats module<stats.html>`_ for statistical analysis
## * `strformat module<strformat.html>`_ for formatting floats for print
## * `system module<system.html>`_ Some very basic and trivial math operators
##   are on system directly, to name a few ``shr``, ``shl``, ``xor``, ``clamp``, etc.


import std/private/since
{.push debugger: off.} # the user does not want to trace a part
                       # of the standard library!

import bitops, fenv

when defined(c) or defined(cpp):
  proc c_isnan(x: float): bool {.importc: "isnan", header: "<math.h>".}
    # a generic like `x: SomeFloat` might work too if this is implemented via a C macro.

func binom*(n, k: int): int =
  ## Computes the `binomial coefficient <https://en.wikipedia.org/wiki/Binomial_coefficient>`_.
  runnableExamples:
    doAssert binom(6, 2) == binom(6, 4)
    doAssert binom(6, 2) == 15
    doAssert binom(-6, 2) == 1
    doAssert binom(6, 0) == 1
  if k <= 0: return 1
  if 2*k > n: return binom(n, n-k)
  result = n
  for i in countup(2, k):
    result = (result * (n + 1 - i)) div i

func createFactTable[N: static[int]]: array[N, int] =
  result[0] = 1
  for i in 1 ..< N:
    result[i] = result[i - 1] * i

func fac*(n: int): int =
  ## Computes the `factorial <https://en.wikipedia.org/wiki/Factorial>`_ of
  ## a non-negative integer ``n``.
  ##
  ## See also:
  ## * `prod func <#prod,openArray[T]>`_
  runnableExamples:
    doAssert fac(3) == 6
    doAssert fac(4) == 24
    doAssert fac(10) == 3628800
  const factTable =
    when sizeof(int) == 2:
      createFactTable[5]()
    elif sizeof(int) == 4:
      createFactTable[13]()
    else:
      createFactTable[21]()
  assert(n >= 0, $n & " must not be negative.")
  assert(n < factTable.len, $n & " is too large to look up in the table")
  factTable[n]

{.push checks: off, line_dir: off, stack_trace: off.}

when defined(Posix) and not defined(genode):
  {.passl: "-lm".}

const
  PI* = 3.1415926535897932384626433          ## The circle constant PI (Ludolph's number)
  TAU* = 2.0 * PI                            ## The circle constant TAU (= 2 * PI)
  E* = 2.71828182845904523536028747          ## Euler's number

  MaxFloat64Precision* = 16                  ## Maximum number of meaningful digits
                                             ## after the decimal point for Nim's
                                             ## ``float64`` type.
  MaxFloat32Precision* = 8                   ## Maximum number of meaningful digits
                                             ## after the decimal point for Nim's
                                             ## ``float32`` type.
  MaxFloatPrecision* = MaxFloat64Precision   ## Maximum number of
                                             ## meaningful digits
                                             ## after the decimal point
                                             ## for Nim's ``float`` type.
  MinFloatNormal* = 2.225073858507201e-308   ## Smallest normal number for Nim's
                                             ## ``float`` type. (= 2^-1022).
  RadPerDeg = PI / 180.0                     ## Number of radians per degree

type
  FloatClass* = enum ## Describes the class a floating point value belongs to.
                     ## This is the type that is returned by
                     ## `classify func <#classify,float>`_.
    fcNormal,        ## value is an ordinary nonzero floating point value
    fcSubnormal,     ## value is a subnormal (a very small) floating point value
    fcZero,          ## value is zero
    fcNegZero,       ## value is the negative zero
    fcNan,           ## value is Not-A-Number (NAN)
    fcInf,           ## value is positive infinity
    fcNegInf         ## value is negative infinity

func isNaN*(x: SomeFloat): bool {.inline, since: (1,5,1).} =
  ## Returns whether `x` is a `NaN`, more efficiently than via `classify(x) == fcNan`.
  ## Works even with: `--passc:-ffast-math`.
  runnableExamples:
    doAssert NaN.isNaN
    doAssert not Inf.isNaN
    doAssert isNaN(Inf - Inf)
    doAssert not isNan(3.1415926)
    doAssert not isNan(0'f32)

  template fn: untyped = result = x != x
  when nimvm: fn()
  else:
    when defined(js): fn()
    else: result = c_isnan(x)

func classify*(x: float): FloatClass =
  ## Classifies a floating point value.
  ##
  ## Returns ``x``'s class as specified by `FloatClass enum<#FloatClass>`_.
  ## Doesn't work with: `--passc:-ffast-math`.
  runnableExamples:
    doAssert classify(0.3) == fcNormal
    doAssert classify(0.0) == fcZero
    doAssert classify(0.3/0.0) == fcInf
    doAssert classify(-0.3/0.0) == fcNegInf
    doAssert classify(5.0e-324) == fcSubnormal

  # JavaScript and most C compilers have no classify:
  if x == 0.0:
    if 1.0/x == Inf:
      return fcZero
    else:
      return fcNegZero
  if x*0.5 == x:
    if x > 0.0: return fcInf
    else: return fcNegInf
  if x != x: return fcNan
  if abs(x) < MinFloatNormal:
    return fcSubnormal
  return fcNormal

func almostEqual*[T: SomeFloat](x, y: T; unitsInLastPlace: Natural = 4): bool {.
    since: (1, 5), inline.} =
  ## Checks if two float values are almost equal, using
  ## `machine epsilon <https://en.wikipedia.org/wiki/Machine_epsilon>`_.
  ##
  ## `unitsInLastPlace` is the max number of
  ## `units in last place <https://en.wikipedia.org/wiki/Unit_in_the_last_place>`_
  ## difference tolerated when comparing two numbers. The larger the value, the
  ## more error is allowed. A ``0`` value means that two numbers must be exactly the
  ## same to be considered equal.
  ##
  ## The machine epsilon has to be scaled to the magnitude of the values used
  ## and multiplied by the desired precision in ULPs unless the difference is
  ## subnormal.
  ##
  # taken from: https://en.cppreference.com/w/cpp/types/numeric_limits/epsilon
  runnableExamples:
    doAssert almostEqual(3.141592653589793, 3.1415926535897936)
    doAssert almostEqual(1.6777215e7'f32, 1.6777216e7'f32)
    doAssert almostEqual(Inf, Inf)
    doAssert almostEqual(-Inf, -Inf)
    doAssert almostEqual(Inf, -Inf) == false
    doAssert almostEqual(-Inf, Inf) == false
    doAssert almostEqual(Inf, NaN) == false
    doAssert almostEqual(NaN, NaN) == false

  if x == y:
    # short circuit exact equality -- needed to catch two infinities of
    # the same sign. And perhaps speeds things up a bit sometimes.
    return true
  let diff = abs(x - y)
  result = diff <= epsilon(T) * abs(x + y) * T(unitsInLastPlace) or
      diff < minimumPositiveValue(T)

func isPowerOfTwo*(x: int): bool =
  ## Returns ``true``, if ``x`` is a power of two, ``false`` otherwise.
  ##
  ## Zero and negative numbers are not a power of two.
  ##
  ## See also:
  ## * `nextPowerOfTwo func<#nextPowerOfTwo,int>`_
  runnableExamples:
    doAssert isPowerOfTwo(16) == true
    doAssert isPowerOfTwo(5) == false
    doAssert isPowerOfTwo(0) == false
    doAssert isPowerOfTwo(-16) == false
  return (x > 0) and ((x and (x - 1)) == 0)

func nextPowerOfTwo*(x: int): int =
  ## Returns ``x`` rounded up to the nearest power of two.
  ##
  ## Zero and negative numbers get rounded up to 1.
  ##
  ## See also:
  ## * `isPowerOfTwo func<#isPowerOfTwo,int>`_
  runnableExamples:
    doAssert nextPowerOfTwo(16) == 16
    doAssert nextPowerOfTwo(5) == 8
    doAssert nextPowerOfTwo(0) == 1
    doAssert nextPowerOfTwo(-16) == 1
  result = x - 1
  when defined(cpu64):
    result = result or (result shr 32)
  when sizeof(int) > 2:
    result = result or (result shr 16)
  when sizeof(int) > 1:
    result = result or (result shr 8)
  result = result or (result shr 4)
  result = result or (result shr 2)
  result = result or (result shr 1)
  result += 1 + ord(x <= 0)

func sum*[T](x: openArray[T]): T =
  ## Computes the sum of the elements in ``x``.
  ##
  ## If ``x`` is empty, 0 is returned.
  ##
  ## See also:
  ## * `prod func <#prod,openArray[T]>`_
  ## * `cumsum func <#cumsum,openArray[T]>`_
  ## * `cumsummed func <#cumsummed,openArray[T]>`_
  runnableExamples:
    doAssert sum([1, 2, 3, 4]) == 10
    doAssert sum([-1.5, 2.7, -0.1]) == 1.1
  for i in items(x): result = result + i

func prod*[T](x: openArray[T]): T =
  ## Computes the product of the elements in ``x``.
  ##
  ## If ``x`` is empty, 1 is returned.
  ##
  ## See also:
  ## * `sum func <#sum,openArray[T]>`_
  ## * `fac func <#fac,int>`_
  runnableExamples:
    doAssert prod([1, 2, 3, 4]) == 24
    doAssert prod([-4, 3, 5]) == -60
  result = 1.T
  for i in items(x): result = result * i

func cumsummed*[T](x: openArray[T]): seq[T] =
  ## Return cumulative (aka prefix) summation of ``x``.
  ##
  ## See also:
  ## * `sum func <#sum,openArray[T]>`_
  ## * `cumsum func <#cumsum,openArray[T]>`_ for the in-place version
  runnableExamples:
    let a = [1, 2, 3, 4]
    doAssert cumsummed(a) == @[1, 3, 6, 10]
  result.setLen(x.len)
  result[0] = x[0]
  for i in 1 ..< x.len: result[i] = result[i-1] + x[i]

func cumsum*[T](x: var openArray[T]) =
  ## Transforms ``x`` in-place (must be declared as `var`) into its
  ## cumulative (aka prefix) summation.
  ##
  ## See also:
  ## * `sum func <#sum,openArray[T]>`_
  ## * `cumsummed func <#cumsummed,openArray[T]>`_ for a version which
  ##   returns cumsummed sequence
  runnableExamples:
    var a = [1, 2, 3, 4]
    cumsum(a)
    doAssert a == @[1, 3, 6, 10]
  for i in 1 ..< x.len: x[i] = x[i-1] + x[i]

when not defined(js): # C
  func sqrt*(x: float32): float32 {.importc: "sqrtf", header: "<math.h>".}
  func sqrt*(x: float64): float64 {.importc: "sqrt", header: "<math.h>".}
    ## Computes the square root of ``x``.
    ##
    ## See also:
    ## * `cbrt func <#cbrt,float64>`_ for cubic root
    ##
    ## .. code-block:: nim
    ##  echo sqrt(4.0)  ## 2.0
    ##  echo sqrt(1.44) ## 1.2
    ##  echo sqrt(-4.0) ## nan
  func cbrt*(x: float32): float32 {.importc: "cbrtf", header: "<math.h>".}
  func cbrt*(x: float64): float64 {.importc: "cbrt", header: "<math.h>".}
    ## Computes the cubic root of ``x``.
    ##
    ## See also:
    ## * `sqrt func <#sqrt,float64>`_ for square root
    ##
    ## .. code-block:: nim
    ##  echo cbrt(8.0)   ## 2.0
    ##  echo cbrt(2.197) ## 1.3
    ##  echo cbrt(-27.0) ## -3.0
  func ln*(x: float32): float32 {.importc: "logf", header: "<math.h>".}
  func ln*(x: float64): float64 {.importc: "log", header: "<math.h>".}
    ## Computes the `natural logarithm <https://en.wikipedia.org/wiki/Natural_logarithm>`_
    ## of ``x``.
    ##
    ## See also:
    ## * `log func <#log,T,T>`_
    ## * `log10 func <#log10,float64>`_
    ## * `log2 func <#log2,float64>`_
    ## * `exp func <#exp,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo ln(exp(4.0)) ## 4.0
    ##  echo ln(1.0))     ## 0.0
    ##  echo ln(0.0)      ## -inf
    ##  echo ln(-7.0)     ## nan
else: # JS
  func sqrt*(x: float32): float32 {.importc: "Math.sqrt", nodecl.}
  func sqrt*(x: float64): float64 {.importc: "Math.sqrt", nodecl.}

  func cbrt*(x: float32): float32 {.importc: "Math.cbrt", nodecl.}
  func cbrt*(x: float64): float64 {.importc: "Math.cbrt", nodecl.}

  func ln*(x: float32): float32 {.importc: "Math.log", nodecl.}
  func ln*(x: float64): float64 {.importc: "Math.log", nodecl.}

func log*[T: SomeFloat](x, base: T): T =
  ## Computes the logarithm of ``x`` to base ``base``.
  ##
  ## See also:
  ## * `ln func <#ln,float64>`_
  ## * `log10 func <#log10,float64>`_
  ## * `log2 func <#log2,float64>`_
  ## * `exp func <#exp,float64>`_
  ##
  ## .. code-block:: nim
  ##  echo log(9.0, 3.0)  ## 2.0
  ##  echo log(32.0, 2.0) ## 5.0
  ##  echo log(0.0, 2.0)  ## -inf
  ##  echo log(-7.0, 4.0) ## nan
  ##  echo log(8.0, -2.0) ## nan
  ln(x) / ln(base)

when not defined(js): # C
  func log10*(x: float32): float32 {.importc: "log10f", header: "<math.h>".}
  func log10*(x: float64): float64 {.importc: "log10", header: "<math.h>".}
    ## Computes the common logarithm (base 10) of ``x``.
    ##
    ## See also:
    ## * `ln func <#ln,float64>`_
    ## * `log func <#log,T,T>`_
    ## * `log2 func <#log2,float64>`_
    ## * `exp func <#exp,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo log10(100.0)  ## 2.0
    ##  echo log10(0.0)    ## nan
    ##  echo log10(-100.0) ## -inf
  func exp*(x: float32): float32 {.importc: "expf", header: "<math.h>".}
  func exp*(x: float64): float64 {.importc: "exp", header: "<math.h>".}
    ## Computes the exponential function of ``x`` (e^x).
    ##
    ## See also:
    ## * `ln func <#ln,float64>`_
    ## * `log func <#log,T,T>`_
    ## * `log10 func <#log10,float64>`_
    ## * `log2 func <#log2,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo exp(1.0)     ## 2.718281828459045
    ##  echo ln(exp(4.0)) ## 4.0
    ##  echo exp(0.0)     ## 1.0
    ##  echo exp(-1.0)    ## 0.3678794411714423
  func sin*(x: float32): float32 {.importc: "sinf", header: "<math.h>".}
  func sin*(x: float64): float64 {.importc: "sin", header: "<math.h>".}
    ## Computes the sine of ``x``.
    ##
    ## See also:
    ## * `cos func <#cos,float64>`_
    ## * `tan func <#tan,float64>`_
    ## * `arcsin func <#arcsin,float64>`_
    ## * `sinh func <#sinh,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo sin(PI / 6)         ## 0.4999999999999999
    ##  echo sin(degToRad(90.0)) ## 1.0
  func cos*(x: float32): float32 {.importc: "cosf", header: "<math.h>".}
  func cos*(x: float64): float64 {.importc: "cos", header: "<math.h>".}
    ## Computes the cosine of ``x``.
    ##
    ## See also:
    ## * `sin func <#sin,float64>`_
    ## * `tan func <#tan,float64>`_
    ## * `arccos func <#arccos,float64>`_
    ## * `cosh func <#cosh,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo cos(2 * PI)         ## 1.0
    ##  echo cos(degToRad(60.0)) ## 0.5000000000000001
  func tan*(x: float32): float32 {.importc: "tanf", header: "<math.h>".}
  func tan*(x: float64): float64 {.importc: "tan", header: "<math.h>".}
    ## Computes the tangent of ``x``.
    ##
    ## See also:
    ## * `sin func <#sin,float64>`_
    ## * `cos func <#cos,float64>`_
    ## * `arctan func <#arctan,float64>`_
    ## * `tanh func <#tanh,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo tan(degToRad(45.0)) ## 0.9999999999999999
    ##  echo tan(PI / 4)         ## 0.9999999999999999
  func sinh*(x: float32): float32 {.importc: "sinhf", header: "<math.h>".}
  func sinh*(x: float64): float64 {.importc: "sinh", header: "<math.h>".}
    ## Computes the `hyperbolic sine <https://en.wikipedia.org/wiki/Hyperbolic_function#Definitions>`_ of ``x``.
    ##
    ## See also:
    ## * `cosh func <#cosh,float64>`_
    ## * `tanh func <#tanh,float64>`_
    ## * `arcsinh func <#arcsinh,float64>`_
    ## * `sin func <#sin,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo sinh(0.0)            ## 0.0
    ##  echo sinh(1.0)            ## 1.175201193643801
    ##  echo sinh(degToRad(90.0)) ## 2.301298902307295
  func cosh*(x: float32): float32 {.importc: "coshf", header: "<math.h>".}
  func cosh*(x: float64): float64 {.importc: "cosh", header: "<math.h>".}
    ## Computes the `hyperbolic cosine <https://en.wikipedia.org/wiki/Hyperbolic_function#Definitions>`_ of ``x``.
    ##
    ## See also:
    ## * `sinh func <#sinh,float64>`_
    ## * `tanh func <#tanh,float64>`_
    ## * `arccosh func <#arccosh,float64>`_
    ## * `cos func <#cos,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo cosh(0.0)            ## 1.0
    ##  echo cosh(1.0)            ## 1.543080634815244
    ##  echo cosh(degToRad(90.0)) ## 2.509178478658057
  func tanh*(x: float32): float32 {.importc: "tanhf", header: "<math.h>".}
  func tanh*(x: float64): float64 {.importc: "tanh", header: "<math.h>".}
    ## Computes the `hyperbolic tangent <https://en.wikipedia.org/wiki/Hyperbolic_function#Definitions>`_ of ``x``.
    ##
    ## See also:
    ## * `sinh func <#sinh,float64>`_
    ## * `cosh func <#cosh,float64>`_
    ## * `arctanh func <#arctanh,float64>`_
    ## * `tan func <#tan,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo tanh(0.0)            ## 0.0
    ##  echo tanh(1.0)            ## 0.7615941559557649
    ##  echo tanh(degToRad(90.0)) ## 0.9171523356672744

  func arccos*(x: float32): float32 {.importc: "acosf", header: "<math.h>".}
  func arccos*(x: float64): float64 {.importc: "acos", header: "<math.h>".}
    ## Computes the arc cosine of ``x``.
    ##
    ## See also:
    ## * `arcsin func <#arcsin,float64>`_
    ## * `arctan func <#arctan,float64>`_
    ## * `arctan2 func <#arctan2,float64,float64>`_
    ## * `cos func <#cos,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo radToDeg(arccos(0.0)) ## 90.0
    ##  echo radToDeg(arccos(1.0)) ## 0.0
  func arcsin*(x: float32): float32 {.importc: "asinf", header: "<math.h>".}
  func arcsin*(x: float64): float64 {.importc: "asin", header: "<math.h>".}
    ## Computes the arc sine of ``x``.
    ##
    ## See also:
    ## * `arccos func <#arccos,float64>`_
    ## * `arctan func <#arctan,float64>`_
    ## * `arctan2 func <#arctan2,float64,float64>`_
    ## * `sin func <#sin,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo radToDeg(arcsin(0.0)) ## 0.0
    ##  echo radToDeg(arcsin(1.0)) ## 90.0
  func arctan*(x: float32): float32 {.importc: "atanf", header: "<math.h>".}
  func arctan*(x: float64): float64 {.importc: "atan", header: "<math.h>".}
    ## Calculate the arc tangent of ``x``.
    ##
    ## See also:
    ## * `arcsin func <#arcsin,float64>`_
    ## * `arccos func <#arccos,float64>`_
    ## * `arctan2 func <#arctan2,float64,float64>`_
    ## * `tan func <#tan,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo arctan(1.0) ## 0.7853981633974483
    ##  echo radToDeg(arctan(1.0)) ## 45.0
  func arctan2*(y, x: float32): float32 {.importc: "atan2f",
      header: "<math.h>".}
  func arctan2*(y, x: float64): float64 {.importc: "atan2", header: "<math.h>".}
    ## Calculate the arc tangent of ``y`` / ``x``.
    ##
    ## It produces correct results even when the resulting angle is near
    ## pi/2 or -pi/2 (``x`` near 0).
    ##
    ## See also:
    ## * `arcsin func <#arcsin,float64>`_
    ## * `arccos func <#arccos,float64>`_
    ## * `arctan func <#arctan,float64>`_
    ## * `tan func <#tan,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo arctan2(1.0, 0.0) ## 1.570796326794897
    ##  echo radToDeg(arctan2(1.0, 0.0)) ## 90.0
  func arcsinh*(x: float32): float32 {.importc: "asinhf", header: "<math.h>".}
  func arcsinh*(x: float64): float64 {.importc: "asinh", header: "<math.h>".}
    ## Computes the inverse hyperbolic sine of ``x``.
  func arccosh*(x: float32): float32 {.importc: "acoshf", header: "<math.h>".}
  func arccosh*(x: float64): float64 {.importc: "acosh", header: "<math.h>".}
    ## Computes the inverse hyperbolic cosine of ``x``.
  func arctanh*(x: float32): float32 {.importc: "atanhf", header: "<math.h>".}
  func arctanh*(x: float64): float64 {.importc: "atanh", header: "<math.h>".}
    ## Computes the inverse hyperbolic tangent of ``x``.

else: # JS
  func log10*(x: float32): float32 {.importc: "Math.log10", nodecl.}
  func log10*(x: float64): float64 {.importc: "Math.log10", nodecl.}
  func log2*(x: float32): float32 {.importc: "Math.log2", nodecl.}
  func log2*(x: float64): float64 {.importc: "Math.log2", nodecl.}
  func exp*(x: float32): float32 {.importc: "Math.exp", nodecl.}
  func exp*(x: float64): float64 {.importc: "Math.exp", nodecl.}

  func sin*[T: float32|float64](x: T): T {.importc: "Math.sin", nodecl.}
  func cos*[T: float32|float64](x: T): T {.importc: "Math.cos", nodecl.}
  func tan*[T: float32|float64](x: T): T {.importc: "Math.tan", nodecl.}

  func sinh*[T: float32|float64](x: T): T {.importc: "Math.sinh", nodecl.}
  func cosh*[T: float32|float64](x: T): T {.importc: "Math.cosh", nodecl.}
  func tanh*[T: float32|float64](x: T): T {.importc: "Math.tanh", nodecl.}

  func arcsin*[T: float32|float64](x: T): T {.importc: "Math.asin", nodecl.}
  func arccos*[T: float32|float64](x: T): T {.importc: "Math.acos", nodecl.}
  func arctan*[T: float32|float64](x: T): T {.importc: "Math.atan", nodecl.}
  func arctan2*[T: float32|float64](y, x: T): T {.importc: "Math.atan2", nodecl.}

  func arcsinh*[T: float32|float64](x: T): T {.importc: "Math.asinh", nodecl.}
  func arccosh*[T: float32|float64](x: T): T {.importc: "Math.acosh", nodecl.}
  func arctanh*[T: float32|float64](x: T): T {.importc: "Math.atanh", nodecl.}

func cot*[T: float32|float64](x: T): T = 1.0 / tan(x)
  ## Computes the cotangent of ``x`` (1 / tan(x)).
func sec*[T: float32|float64](x: T): T = 1.0 / cos(x)
  ## Computes the secant of ``x`` (1 / cos(x)).
func csc*[T: float32|float64](x: T): T = 1.0 / sin(x)
  ## Computes the cosecant of ``x`` (1 / sin(x)).

func coth*[T: float32|float64](x: T): T = 1.0 / tanh(x)
  ## Computes the hyperbolic cotangent of ``x`` (1 / tanh(x)).
func sech*[T: float32|float64](x: T): T = 1.0 / cosh(x)
  ## Computes the hyperbolic secant of ``x`` (1 / cosh(x)).
func csch*[T: float32|float64](x: T): T = 1.0 / sinh(x)
  ## Computes the hyperbolic cosecant of ``x`` (1 / sinh(x)).

func arccot*[T: float32|float64](x: T): T = arctan(1.0 / x)
  ## Computes the inverse cotangent of ``x``.
func arcsec*[T: float32|float64](x: T): T = arccos(1.0 / x)
  ## Computes the inverse secant of ``x``.
func arccsc*[T: float32|float64](x: T): T = arcsin(1.0 / x)
  ## Computes the inverse cosecant of ``x``.

func arccoth*[T: float32|float64](x: T): T = arctanh(1.0 / x)
  ## Computes the inverse hyperbolic cotangent of ``x``.
func arcsech*[T: float32|float64](x: T): T = arccosh(1.0 / x)
  ## Computes the inverse hyperbolic secant of ``x``.
func arccsch*[T: float32|float64](x: T): T = arcsinh(1.0 / x)
  ## Computes the inverse hyperbolic cosecant of ``x``.

const windowsCC89 = defined(windows) and defined(bcc)

when not defined(js): # C
  func hypot*(x, y: float32): float32 {.importc: "hypotf", header: "<math.h>".}
  func hypot*(x, y: float64): float64 {.importc: "hypot", header: "<math.h>".}
    ## Computes the hypotenuse of a right-angle triangle with ``x`` and
    ## ``y`` as its base and height. Equivalent to ``sqrt(x*x + y*y)``.
    ##
    ## .. code-block:: nim
    ##  echo hypot(4.0, 3.0) ## 5.0
  func pow*(x, y: float32): float32 {.importc: "powf", header: "<math.h>".}
  func pow*(x, y: float64): float64 {.importc: "pow", header: "<math.h>".}
    ## Computes x to power raised of y.
    ##
    ## To compute power between integers (e.g. 2^6), use `^ func<#^,T,Natural>`_.
    ##
    ## See also:
    ## * `^ func<#^,T,Natural>`_
    ## * `sqrt func <#sqrt,float64>`_
    ## * `cbrt func <#cbrt,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo pow(100, 1.5)  ## 1000.0
    ##  echo pow(16.0, 0.5) ## 4.0

  # TODO: add C89 version on windows
  when not windowsCC89:
    func erf*(x: float32): float32 {.importc: "erff", header: "<math.h>".}
    func erf*(x: float64): float64 {.importc: "erf", header: "<math.h>".}
      ## Computes the `error function <https://en.wikipedia.org/wiki/Error_function>`_ for ``x``.
      ##
      ## Note: Not available for JS backend.
    func erfc*(x: float32): float32 {.importc: "erfcf", header: "<math.h>".}
    func erfc*(x: float64): float64 {.importc: "erfc", header: "<math.h>".}
      ## Computes the `complementary error function <https://en.wikipedia.org/wiki/Error_function#Complementary_error_function>`_ for ``x``.
      ##
      ## Note: Not available for JS backend.
    func gamma*(x: float32): float32 {.importc: "tgammaf", header: "<math.h>".}
    func gamma*(x: float64): float64 {.importc: "tgamma", header: "<math.h>".}
      ## Computes the `gamma function <https://en.wikipedia.org/wiki/Gamma_function>`_ for ``x``.
      ##
      ## Note: Not available for JS backend.
      ##
      ## See also:
      ## * `lgamma func <#lgamma,float64>`_ for a natural log of gamma function
      ##
      ## .. code-block:: Nim
      ##  echo gamma(1.0)  # 1.0
      ##  echo gamma(4.0)  # 6.0
      ##  echo gamma(11.0) # 3628800.0
      ##  echo gamma(-1.0) # nan
    func lgamma*(x: float32): float32 {.importc: "lgammaf", header: "<math.h>".}
    func lgamma*(x: float64): float64 {.importc: "lgamma", header: "<math.h>".}
      ## Computes the natural log of the gamma function for ``x``.
      ##
      ## Note: Not available for JS backend.
      ##
      ## See also:
      ## * `gamma func <#gamma,float64>`_ for gamma function
      ##
      ## .. code-block:: Nim
      ##  echo lgamma(1.0)  # 1.0
      ##  echo lgamma(4.0)  # 1.791759469228055
      ##  echo lgamma(11.0) # 15.10441257307552
      ##  echo lgamma(-1.0) # inf

  func floor*(x: float32): float32 {.importc: "floorf", header: "<math.h>".}
  func floor*(x: float64): float64 {.importc: "floor", header: "<math.h>".}
    ## Computes the floor function (i.e., the largest integer not greater than ``x``).
    ##
    ## See also:
    ## * `ceil func <#ceil,float64>`_
    ## * `round func <#round,float64>`_
    ## * `trunc func <#trunc,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo floor(2.1)  ## 2.0
    ##  echo floor(2.9)  ## 2.0
    ##  echo floor(-3.5) ## -4.0

  func ceil*(x: float32): float32 {.importc: "ceilf", header: "<math.h>".}
  func ceil*(x: float64): float64 {.importc: "ceil", header: "<math.h>".}
    ## Computes the ceiling function (i.e., the smallest integer not smaller
    ## than ``x``).
    ##
    ## See also:
    ## * `floor func <#floor,float64>`_
    ## * `round func <#round,float64>`_
    ## * `trunc func <#trunc,float64>`_
    ##
    ## .. code-block:: nim
    ##  echo ceil(2.1)  ## 3.0
    ##  echo ceil(2.9)  ## 3.0
    ##  echo ceil(-2.1) ## -2.0

  when windowsCC89:
    # MSVC 2010 don't have trunc/truncf
    # this implementation was inspired by Go-lang Math.Trunc
    func truncImpl(f: float64): float64 =
      const
        mask: uint64 = 0x7FF
        shift: uint64 = 64 - 12
        bias: uint64 = 0x3FF

      if f < 1:
        if f < 0: return -truncImpl(-f)
        elif f == 0: return f # Return -0 when f == -0
        else: return 0

      var x = cast[uint64](f)
      let e = (x shr shift) and mask - bias

      # Keep the top 12+e bits, the integer part; clear the rest.
      if e < 64-12:
        x = x and (not (1'u64 shl (64'u64-12'u64-e) - 1'u64))

      result = cast[float64](x)

    func truncImpl(f: float32): float32 =
      const
        mask: uint32 = 0xFF
        shift: uint32 = 32 - 9
        bias: uint32 = 0x7F

      if f < 1:
        if f < 0: return -truncImpl(-f)
        elif f == 0: return f # Return -0 when f == -0
        else: return 0

      var x = cast[uint32](f)
      let e = (x shr shift) and mask - bias

      # Keep the top 9+e bits, the integer part; clear the rest.
      if e < 32-9:
        x = x and (not (1'u32 shl (32'u32-9'u32-e) - 1'u32))

      result = cast[float32](x)

    func trunc*(x: float64): float64 =
      if classify(x) in {fcZero, fcNegZero, fcNan, fcInf, fcNegInf}: return x
      result = truncImpl(x)

    func trunc*(x: float32): float32 =
      if classify(x) in {fcZero, fcNegZero, fcNan, fcInf, fcNegInf}: return x
      result = truncImpl(x)

    func round*[T: float32|float64](x: T): T =
      ## Windows compilers prior to MSVC 2012 do not implement 'round',
      ## 'roundl' or 'roundf'.
      result = if x < 0.0: ceil(x - T(0.5)) else: floor(x + T(0.5))
  else:
    func round*(x: float32): float32 {.importc: "roundf", header: "<math.h>".}
    func round*(x: float64): float64 {.importc: "round", header: "<math.h>".}
      ## Rounds a float to zero decimal places.
      ##
      ## Used internally by the `round func <#round,T,int>`_
      ## when the specified number of places is 0.
      ##
      ## See also:
      ## * `round func <#round,T,int>`_ for rounding to the specific
      ##   number of decimal places
      ## * `floor func <#floor,float64>`_
      ## * `ceil func <#ceil,float64>`_
      ## * `trunc func <#trunc,float64>`_
      ##
      ## .. code-block:: nim
      ##   echo round(3.4) ## 3.0
      ##   echo round(3.5) ## 4.0
      ##   echo round(4.5) ## 5.0

    func trunc*(x: float32): float32 {.importc: "truncf", header: "<math.h>".}
    func trunc*(x: float64): float64 {.importc: "trunc", header: "<math.h>".}
      ## Truncates ``x`` to the decimal point.
      ##
      ## See also:
      ## * `floor func <#floor,float64>`_
      ## * `ceil func <#ceil,float64>`_
      ## * `round func <#round,float64>`_
      ##
      ## .. code-block:: nim
      ##  echo trunc(PI) # 3.0
      ##  echo trunc(-1.85) # -1.0

  func `mod`*(x, y: float32): float32 {.importc: "fmodf", header: "<math.h>".}
  func `mod`*(x, y: float64): float64 {.importc: "fmod", header: "<math.h>".}
    ## Computes the modulo operation for float values (the remainder of ``x`` divided by ``y``).
    ##
    ## See also:
    ## * `floorMod func <#floorMod,T,T>`_ for Python-like (% operator) behavior
    ##
    ## .. code-block:: nim
    ##  ( 6.5 mod  2.5) ==  1.5
    ##  (-6.5 mod  2.5) == -1.5
    ##  ( 6.5 mod -2.5) ==  1.5
    ##  (-6.5 mod -2.5) == -1.5

else: # JS
  func hypot*(x, y: float32): float32 {.importc: "Math.hypot", varargs, nodecl.}
  func hypot*(x, y: float64): float64 {.importc: "Math.hypot", varargs, nodecl.}
  func pow*(x, y: float32): float32 {.importc: "Math.pow", nodecl.}
  func pow*(x, y: float64): float64 {.importc: "Math.pow", nodecl.}
  func floor*(x: float32): float32 {.importc: "Math.floor", nodecl.}
  func floor*(x: float64): float64 {.importc: "Math.floor", nodecl.}
  func ceil*(x: float32): float32 {.importc: "Math.ceil", nodecl.}
  func ceil*(x: float64): float64 {.importc: "Math.ceil", nodecl.}
  func round*(x: float): float {.importc: "Math.round", nodecl.}
  func trunc*(x: float32): float32 {.importc: "Math.trunc", nodecl.}
  func trunc*(x: float64): float64 {.importc: "Math.trunc", nodecl.}

  func `mod`*(x, y: float32): float32 {.importcpp: "# % #".}
  func `mod`*(x, y: float64): float64 {.importcpp: "# % #".}
    ## Computes the modulo operation for float values (the remainder of ``x`` divided by ``y``).
    ##
    ## .. code-block:: nim
    ##  ( 6.5 mod  2.5) ==  1.5
    ##  (-6.5 mod  2.5) == -1.5
    ##  ( 6.5 mod -2.5) ==  1.5
    ##  (-6.5 mod -2.5) == -1.5

func round*[T: float32|float64](x: T, places: int): T =
  ## Decimal rounding on a binary floating point number.
  ##
  ## This function is NOT reliable. Floating point numbers cannot hold
  ## non integer decimals precisely. If ``places`` is 0 (or omitted),
  ## round to the nearest integral value following normal mathematical
  ## rounding rules (e.g.  ``round(54.5) -> 55.0``). If ``places`` is
  ## greater than 0, round to the given number of decimal places,
  ## e.g. ``round(54.346, 2) -> 54.350000000000001421…``. If ``places`` is negative, round
  ## to the left of the decimal place, e.g. ``round(537.345, -1) ->
  ## 540.0``
  ##
  ## .. code-block:: Nim
  ##  echo round(PI, 2) ## 3.14
  ##  echo round(PI, 4) ## 3.1416
  if places == 0:
    result = round(x)
  else:
    var mult = pow(10.0, places.T)
    result = round(x*mult)/mult

func floorDiv*[T: SomeInteger](x, y: T): T =
  ## Floor division is conceptually defined as ``floor(x / y)``.
  ##
  ## This is different from the `system.div <system.html#div,int,int>`_
  ## operator, which is defined as ``trunc(x / y)``.
  ## That is, ``div`` rounds towards ``0`` and ``floorDiv`` rounds down.
  ##
  ## See also:
  ## * `system.div proc <system.html#div,int,int>`_ for integer division
  ## * `floorMod func <#floorMod,T,T>`_ for Python-like (% operator) behavior
  ##
  ## .. code-block:: nim
  ##  echo floorDiv( 13,  3) #  4
  ##  echo floorDiv(-13,  3) # -5
  ##  echo floorDiv( 13, -3) # -5
  ##  echo floorDiv(-13, -3) #  4
  result = x div y
  let r = x mod y
  if (r > 0 and y < 0) or (r < 0 and y > 0): result.dec 1

func floorMod*[T: SomeNumber](x, y: T): T =
  ## Floor modulus is conceptually defined as ``x - (floorDiv(x, y) * y)``.
  ##
  ## This func behaves the same as the ``%`` operator in Python.
  ##
  ## See also:
  ## * `mod func <#mod,float64,float64>`_
  ## * `floorDiv func <#floorDiv,T,T>`_
  ##
  ## .. code-block:: nim
  ##  echo floorMod( 13,  3) #  1
  ##  echo floorMod(-13,  3) #  2
  ##  echo floorMod( 13, -3) # -2
  ##  echo floorMod(-13, -3) # -1
  result = x mod y
  if (result > 0 and y < 0) or (result < 0 and y > 0): result += y

when not defined(js):
  func c_frexp*(x: float32, exponent: var int32): float32 {.
      importc: "frexp", header: "<math.h>".}
  func c_frexp*(x: float64, exponent: var int32): float64 {.
      importc: "frexp", header: "<math.h>".}
  func frexp*[T, U](x: T, exponent: var U): T =
    ## Split a number into mantissa and exponent.
    ##
    ## ``frexp`` calculates the mantissa m (a float greater than or equal to 0.5
    ## and less than 1) and the integer value n such that ``x`` (the original
    ## float value) equals ``m * 2**n``. frexp stores n in `exponent` and returns
    ## m.
    ##
    runnableExamples:
      var x: int
      doAssert frexp(5.0, x) == 0.625
      doAssert x == 3
    var exp: int32
    result = c_frexp(x, exp)
    exponent = exp

  when windowsCC89:
    # taken from Go-lang Math.Log2
    const ln2 = 0.693147180559945309417232121458176568075500134360255254120680009
    template log2Impl[T](x: T): T =
      var exp: int32
      var frac = frexp(x, exp)
      # Make sure exact powers of two give an exact answer.
      # Don't depend on Log(0.5)*(1/Ln2)+exp being exactly exp-1.
      if frac == 0.5: return T(exp - 1)
      log10(frac)*(1/ln2) + T(exp)

    func log2*(x: float32): float32 = log2Impl(x)
    func log2*(x: float64): float64 = log2Impl(x)
      ## Log2 returns the binary logarithm of x.
      ## The special cases are the same as for Log.

  else:
    func log2*(x: float32): float32 {.importc: "log2f", header: "<math.h>".}
    func log2*(x: float64): float64 {.importc: "log2", header: "<math.h>".}
      ## Computes the binary logarithm (base 2) of ``x``.
      ##
      ## See also:
      ## * `log func <#log,T,T>`_
      ## * `log10 func <#log10,float64>`_
      ## * `ln func <#ln,float64>`_
      ## * `exp func <#exp,float64>`_
      ##
      ## .. code-block:: Nim
      ##  echo log2(8.0)  # 3.0
      ##  echo log2(1.0)  # 0.0
      ##  echo log2(0.0)  # -inf
      ##  echo log2(-2.0) # nan

else:
  func frexp*[T: float32|float64](x: T, exponent: var int): T =
    if x == 0.0:
      exponent = 0
      result = 0.0
    elif x < 0.0:
      result = -frexp(-x, exponent)
    else:
      var ex = trunc(log2(x))
      exponent = int(ex)
      result = x / pow(2.0, ex)
      if abs(result) >= 1:
        inc(exponent)
        result = result / 2
      if exponent == 1024 and result == 0.0:
        result = 0.99999999999999988898

func splitDecimal*[T: float32|float64](x: T): tuple[intpart: T, floatpart: T] =
  ## Breaks ``x`` into an integer and a fractional part.
  ##
  ## Returns a tuple containing ``intpart`` and ``floatpart`` representing
  ## the integer part and the fractional part respectively.
  ##
  ## Both parts have the same sign as ``x``.  Analogous to the ``modf``
  ## function in C.
  ##
  runnableExamples:
    doAssert splitDecimal(5.25) == (intpart: 5.0, floatpart: 0.25)
    doAssert splitDecimal(-2.73) == (intpart: -2.0, floatpart: -0.73)
  var
    absolute: T
  absolute = abs(x)
  result.intpart = floor(absolute)
  result.floatpart = absolute - result.intpart
  if x < 0:
    result.intpart = -result.intpart
    result.floatpart = -result.floatpart


func degToRad*[T: float32|float64](d: T): T {.inline.} =
  ## Convert from degrees to radians.
  ##
  ## See also:
  ## * `radToDeg func <#radToDeg,T>`_
  ##
  runnableExamples:
    doAssert degToRad(180.0) == 3.141592653589793
  result = T(d) * RadPerDeg

func radToDeg*[T: float32|float64](d: T): T {.inline.} =
  ## Convert from radians to degrees.
  ##
  ## See also:
  ## * `degToRad func <#degToRad,T>`_
  ##
  runnableExamples:
    doAssert radToDeg(2 * PI) == 360.0
  result = T(d) / RadPerDeg

func sgn*[T: SomeNumber](x: T): int {.inline.} =
  ## Sign function.
  ##
  ## Returns:
  ## * `-1` for negative numbers and ``NegInf``,
  ## * `1` for positive numbers and ``Inf``,
  ## * `0` for positive zero, negative zero and ``NaN``
  ##
  runnableExamples:
    doAssert sgn(5) == 1
    doAssert sgn(0) == 0
    doAssert sgn(-4.1) == -1
  ord(T(0) < x) - ord(x < T(0))

{.pop.}
{.pop.}

func `^`*[T: SomeNumber](x: T, y: Natural): T =
  ## Computes ``x`` to the power ``y``.
  ##
  ## Exponent ``y`` must be non-negative, use
  ## `pow func <#pow,float64,float64>`_ for negative exponents.
  ##
  ## See also:
  ## * `pow func <#pow,float64,float64>`_ for negative exponent or
  ##   floats
  ## * `sqrt func <#sqrt,float64>`_
  ## * `cbrt func <#cbrt,float64>`_
  ##
  runnableExamples:
    assert -3.0^0 == 1.0
    assert -3^1 == -3
    assert -3^2 == 9
    assert -3.0^3 == -27.0
    assert -3.0^4 == 81.0

  case y
  of 0: result = 1
  of 1: result = x
  of 2: result = x * x
  of 3: result = x * x * x
  else:
    var (x, y) = (x, y)
    result = 1
    while true:
      if (y and 1) != 0:
        result *= x
      y = y shr 1
      if y == 0:
        break
      x *= x

func gcd*[T](x, y: T): T =
  ## Computes the greatest common (positive) divisor of ``x`` and ``y``.
  ##
  ## Note that for floats, the result cannot always be interpreted as
  ## "greatest decimal `z` such that ``z*N == x and z*M == y``
  ## where N and M are positive integers."
  ##
  ## See also:
  ## * `gcd func <#gcd,SomeInteger,SomeInteger>`_ for integer version
  ## * `lcm func <#lcm,T,T>`_
  runnableExamples:
    doAssert gcd(13.5, 9.0) == 4.5
  var (x, y) = (x, y)
  while y != 0:
    x = x mod y
    swap x, y
  abs x

func gcd*(x, y: SomeInteger): SomeInteger =
  ## Computes the greatest common (positive) divisor of ``x`` and ``y``,
  ## using binary GCD (aka Stein's) algorithm.
  ##
  ## See also:
  ## * `gcd func <#gcd,T,T>`_ for floats version
  ## * `lcm func <#lcm,T,T>`_
  runnableExamples:
    doAssert gcd(12, 8) == 4
    doAssert gcd(17, 63) == 1
  when x is SomeSignedInt:
    var x = abs(x)
  else:
    var x = x
  when y is SomeSignedInt:
    var y = abs(y)
  else:
    var y = y

  if x == 0:
    return y
  if y == 0:
    return x

  let shift = countTrailingZeroBits(x or y)
  y = y shr countTrailingZeroBits(y)
  while x != 0:
    x = x shr countTrailingZeroBits(x)
    if y > x:
      swap y, x
    x -= y
  y shl shift

func gcd*[T](x: openArray[T]): T {.since: (1, 1).} =
  ## Computes the greatest common (positive) divisor of the elements of ``x``.
  ##
  ## See also:
  ## * `gcd func <#gcd,T,T>`_ for integer version
  runnableExamples:
    doAssert gcd(@[13.5, 9.0]) == 4.5
  result = x[0]
  var i = 1
  while i < x.len:
    result = gcd(result, x[i])
    inc(i)

func lcm*[T](x, y: T): T =
  ## Computes the least common multiple of ``x`` and ``y``.
  ##
  ## See also:
  ## * `gcd func <#gcd,T,T>`_
  runnableExamples:
    doAssert lcm(24, 30) == 120
    doAssert lcm(13, 39) == 39
  x div gcd(x, y) * y

func lcm*[T](x: openArray[T]): T {.since: (1, 1).} =
  ## Computes the least common multiple of the elements of ``x``.
  ##
  ## See also:
  ## * `gcd func <#gcd,T,T>`_ for integer version
  runnableExamples:
    doAssert lcm(@[24, 30]) == 120
  result = x[0]
  var i = 1
  while i < x.len:
    result = lcm(result, x[i])
    inc(i)
