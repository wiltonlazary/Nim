

type
  Int128* = object
    udata: array[4,uint32]

template sdata(arg: Int128, idx: int): int32 =
  # udata and sdata was supposed to be in a union, but unions are
  # handled incorrectly in the VM.
  cast[ptr int32](arg.udata[idx].unsafeAddr)[]

# encoding least significant int first (like LittleEndian)

type
  InvalidArgument = object of Exception

template require(cond: bool) =
  if unlikely(not cond):
    raise newException(InvalidArgument, "")

const
  Zero* = Int128(udata: [0'u32,0,0,0])
  One* = Int128(udata: [1'u32,0,0,0])
  Ten* = Int128(udata: [10'u32,0,0,0])
  Min = Int128(udata: [0'u32,0,0,0x80000000'u32])
  Max = Int128(udata: [high(uint32),high(uint32),high(uint32),uint32(high(int32))])

template low*(t: typedesc[Int128]): Int128 = Min
template high*(t: typedesc[Int128]): Int128 = Max

proc `$`*(a: Int128): string

proc toInt128*[T: SomeInteger](arg: T): Int128 =
  when T is SomeUnsignedInt:
    when sizeof(arg) <= 4:
      result.udata[0] = uint32(arg)
    else:
      result.udata[0] = uint32(arg and T(0xffffffff))
      result.udata[1] = uint32(arg shr 32)
  else:
    when sizeof(arg) <= 4:
      result.sdata(0) = int32(arg)
      if arg < 0: # sign extend
        result.sdata(1) = -1
        result.sdata(2) = -1
        result.sdata(3) = -1
    else:
      let tmp = int64(arg)
      result.udata[0] = uint32(tmp and 0xffffffff)
      result.sdata(1) = int32(tmp shr 32)
      if arg < 0: # sign extend
        result.sdata(2) = -1
        result.sdata(3) = -1

template isNegative(arg: Int128): bool =
  arg.sdata(3) < 0

template isNegative(arg: int32): bool =
  arg < 0

proc bitconcat(a,b: uint32): uint64 =
  (uint64(a) shl 32) or uint64(b)

proc bitsplit(a: uint64): (uint32,uint32) =
  (cast[uint32](a shr 32), cast[uint32](a))

proc toInt64*(arg: Int128): int64 =
  if isNegative(arg):
    assert(arg.sdata(3) == -1, "out of range")
    assert(arg.sdata(2) == -1, "out of range")
  else:
    assert(arg.sdata(3) == 0, "out of range")
    assert(arg.sdata(2) == 0, "out of range")

  cast[int64](bitconcat(arg.udata[1], arg.udata[0]))

proc toUInt64*(arg: Int128): uint64 =
  assert(arg.udata[3] == 0)
  assert(arg.udata[2] == 0)
  bitconcat(arg.udata[1], arg.udata[0])

proc addToHex(result: var string; arg: uint32) =
  for i in 0 ..< 8:
    let idx = (arg shr ((7-i) * 4)) and 0xf
    result.add "0123456789abcdef"[idx]

proc addToHex*(result: var string; arg: Int128) =
  var i = 3
  while i >= 0:
    result.addToHex(arg.udata[i])
    i -= 1

proc toHex*(arg: Int128): string =
  result.addToHex(arg)

proc inc*(a: var Int128, y: uint32 = 1) =
  let input = a
  a.udata[0] += y
  if unlikely(a.udata[0] < y):
    a.udata[1].inc
    if unlikely(a.udata[1] == 0):
      a.udata[2].inc
      if unlikely(a.udata[2] == 0):
        a.udata[3].inc
        doAssert(a.sdata(3) != low(int32), "overflow")

proc cmp*(a,b: Int128): int =
  let tmp1 = cmp(a.sdata(3), b.sdata(3))
  if tmp1 != 0: return tmp1
  let tmp2 = cmp(a.udata[2], b.udata[2])
  if tmp2 != 0: return tmp2
  let tmp3 = cmp(a.udata[1], b.udata[1])
  if tmp3 != 0: return tmp3
  let tmp4 = cmp(a.udata[0], b.udata[0])
  return tmp4

proc `<`*(a,b: Int128): bool =
  cmp(a,b) < 0

proc `<=`*(a,b: Int128): bool =
  cmp(a,b) <= 0

proc `==`*(a,b: Int128): bool =
  if a.udata[0] != b.udata[0]: return false
  if a.udata[1] != b.udata[1]: return false
  if a.udata[2] != b.udata[2]: return false
  if a.udata[3] != b.udata[3]: return false
  return true

proc inplaceBitnot(a: var Int128) =
  a.udata[0] = not a.udata[0]
  a.udata[1] = not a.udata[1]
  a.udata[2] = not a.udata[2]
  a.udata[3] = not a.udata[3]

proc bitnot*(a: Int128): Int128 =
  result.udata[0] = not a.udata[0]
  result.udata[1] = not a.udata[1]
  result.udata[2] = not a.udata[2]
  result.udata[3] = not a.udata[3]

proc bitand*(a,b: Int128): Int128 =
  result.udata[0] = a.udata[0] and b.udata[0]
  result.udata[1] = a.udata[1] and b.udata[1]
  result.udata[2] = a.udata[2] and b.udata[2]
  result.udata[3] = a.udata[3] and b.udata[3]

proc bitor*(a,b: Int128): Int128 =
  result.udata[0] = a.udata[0] or b.udata[0]
  result.udata[1] = a.udata[1] or b.udata[1]
  result.udata[2] = a.udata[2] or b.udata[2]
  result.udata[3] = a.udata[3] or b.udata[3]

proc bitxor*(a,b: Int128): Int128 =
  result.udata[0] = a.udata[0] xor b.udata[0]
  result.udata[1] = a.udata[1] xor b.udata[1]
  result.udata[2] = a.udata[2] xor b.udata[2]
  result.udata[3] = a.udata[3] xor b.udata[3]

proc `shr`*(a: Int128, b: int): Int128 =
  let b = b and 127
  if b < 32:
    result.sdata(3) = a.sdata(3) shr b
    result.udata[2] = cast[uint32](bitconcat(a.udata[3], a.udata[2]) shr b)
    result.udata[1] = cast[uint32](bitconcat(a.udata[2], a.udata[1]) shr b)
    result.udata[0] = cast[uint32](bitconcat(a.udata[1], a.udata[0]) shr b)
  elif b < 64:
    if isNegative(a):
      result.sdata(3) = -1
    result.sdata(2) = a.sdata(3) shr (b and 31)
    result.udata[1] = cast[uint32](bitconcat(a.udata[2], a.udata[1]) shr (b and 31))
    result.udata[0] = cast[uint32](bitconcat(a.udata[1], a.udata[0]) shr (b and 31))
  elif b < 96:
    if isNegative(a):
      result.sdata(3) = -1
      result.sdata(2) = -1
    result.sdata(1) = a.sdata(3) shr (b and 31)
    result.udata[0] = cast[uint32](bitconcat(a.udata[1], a.udata[0]) shr (b and 31))
  else: # b < 128
    if isNegative(a):
      result.sdata(3) = -1
      result.sdata(2) = -1
      result.sdata(1) = -1
    result.sdata(0) = a.sdata(3) shr (b and 31)

proc `shl`*(a: Int128, b: int): Int128 =
  let b = b and 127
  if b < 32:
    result.udata[0] = a.udata[0] shl b
    result.udata[1] = cast[uint32]((bitconcat(a.udata[1], a.udata[0]) shl b) shr 32)
    result.udata[2] = cast[uint32]((bitconcat(a.udata[2], a.udata[1]) shl b) shr 32)
    result.udata[3] = cast[uint32]((bitconcat(a.udata[3], a.udata[2]) shl b) shr 32)
  elif b < 64:
    result.udata[0] = 0
    result.udata[1] = a.udata[0] shl (b and 31)
    result.udata[2] = cast[uint32]((bitconcat(a.udata[1], a.udata[0]) shl (b and 31)) shr 32)
    result.udata[3] = cast[uint32]((bitconcat(a.udata[2], a.udata[1]) shl (b and 31)) shr 32)
  elif b < 96:
    result.udata[0] = 0
    result.udata[1] = 0
    result.udata[2] = a.udata[0] shl (b and 31)
    result.udata[3] = cast[uint32]((bitconcat(a.udata[1], a.udata[0]) shl (b and 31)) shr 32)
  else:
    result.udata[0] = 0
    result.udata[1] = 0
    result.udata[2] = 0
    result.udata[3] = a.udata[0] shl (b and 31)


proc `+`*(a,b: Int128): Int128 =
  let tmp0 = uint64(a.udata[0]) + uint64(b.udata[0])
  result.udata[0] = cast[uint32](tmp0)
  let tmp1 = uint64(a.udata[1]) + uint64(b.udata[1]) + (tmp0 shr 32)
  result.udata[1] = cast[uint32](tmp1)
  let tmp2 = uint64(a.udata[2]) + uint64(b.udata[2]) + (tmp1 shr 32)
  result.udata[2] = cast[uint32](tmp2)
  let tmp3 = uint64(a.udata[3]) + uint64(b.udata[3]) + (tmp2 shr 32)
  result.udata[3] = cast[uint32](tmp3)

proc `+=`*(a: var Int128, b: Int128) =
  a = a + b

proc `-`*(a: Int128): Int128 =
  result = bitnot(a)
  result.inc

proc `-`*(a,b: Int128): Int128 =
  a + (-b)

proc `-=`*(a: var Int128, b: Int128) =
  a = a - b

proc abs*(a: Int128): Int128 =
  if isNegative(a):
    -a
  else:
    a

proc abs(a: int32): int =
  if a < 0: -a else: a

proc `*`(a: Int128, b: uint32): Int128 =
  let tmp0 = uint64(a.udata[0]) * uint64(b)
  let tmp1 = uint64(a.udata[1]) * uint64(b)
  let tmp2 = uint64(a.udata[2]) * uint64(b)
  let tmp3 = uint64(a.udata[3]) * uint64(b)

  if unlikely(tmp3 > uint64(high(int32))):
    assert(false, "overflow")

  result.udata[0] = cast[uint32](tmp0)
  result.udata[1] = cast[uint32](tmp1) + cast[uint32](tmp0 shr 32)
  result.udata[2] = cast[uint32](tmp2) + cast[uint32](tmp1 shr 32)
  result.udata[3] = cast[uint32](tmp3) + cast[uint32](tmp2 shr 32)

proc `*`*(a: Int128, b: int32): Int128 =
  let isNegative = isNegative(a) xor isNegative(b)
  result = a * cast[uint32](abs(b))
  if b < 0:
    result = -result

proc `*=`*(a: var Int128, b: int32): Int128 =
  result = result * b

proc makeInt128(high,low: uint64): Int128 =
  result.udata[0] = cast[uint32](low)
  result.udata[1] = cast[uint32](low shr 32)
  result.udata[2] = cast[uint32](high)
  result.udata[3] = cast[uint32](high shr 32)

proc high64(a: Int128): uint64 =
  bitconcat(a.udata[3], a.udata[2])

proc low64(a: Int128): uint64 =
  bitconcat(a.udata[1], a.udata[0])

proc `*`*(lhs,rhs: Int128): Int128 =
  let isNegative = isNegative(lhs) xor isNegative(rhs)

  let
    a = cast[uint64](lhs.udata[0])
    b = cast[uint64](lhs.udata[1])
    c = cast[uint64](lhs.udata[2])
    d = cast[uint64](lhs.udata[3])

    e = cast[uint64](rhs.udata[0])
    f = cast[uint64](rhs.udata[1])
    g = cast[uint64](rhs.udata[2])
    h = cast[uint64](rhs.udata[3])


  let a32 = cast[uint64](lhs.udata[1])
  let a00 = cast[uint64](lhs.udata[0])
  let b32 = cast[uint64](rhs.udata[1])
  let b00 = cast[uint64](rhs.udata[0])

  result = makeInt128(high64(lhs) * low64(rhs) + low64(lhs) * high64(rhs) + a32 * b32, a00 * b00)
  result = result + toInt128(a32 * b00) shl 32
  result = result + toInt128(a00 * b32) shl 32

  if isNegative != isNegative(result):
    echo result
    assert(false, "overflow")

proc `*=`*(a: var Int128, b: Int128) =
  a = a * b

import bitops

proc fastLog2*(a: Int128): int =
  if a.udata[3] != 0:
    return 96 + fastLog2(a.udata[3])
  if a.udata[2] != 0:
    return 64 + fastLog2(a.udata[2])
  if a.udata[1] != 0:
    return 32 + fastLog2(a.udata[1])
  if a.udata[0] != 0:
    return      fastLog2(a.udata[0])

proc divMod*(dividend, divisor: Int128): tuple[quotient, remainder: Int128] =
  assert(divisor != Zero)
  let isNegative = isNegative(dividend) xor isNegative(divisor)

  var dividend = abs(dividend)
  let divisor = abs(divisor)

  if divisor > dividend:
    result.quotient = Zero
    result.remainder = dividend
    return

  if divisor == dividend:
    result.quotient = One
    result.remainder = Zero
    return

  var denominator = divisor
  var quotient = Zero

  # Left aligns the MSB of the denominator and the dividend.
  let shift = fastLog2(dividend) - fastLog2(denominator)
  denominator = denominator shl shift

  # Uses shift-subtract algorithm to divide dividend by denominator. The
  # remainder will be left in dividend.
  for i in 0 .. shift:
    quotient = quotient shl 1
    if dividend >= denominator:
      dividend = dividend - denominator
      quotient = bitor(quotient, One)

    denominator = denominator shr 1

  result.quotient = quotient
  result.remainder = dividend

proc `div`*(a,b: Int128): Int128 =
  let (a,b) = divMod(a,b)
  return a

proc `mod`*(a,b: Int128): Int128 =
  let (a,b) = divMod(a,b)
  return b

proc `$`*(a: Int128): string =
  if a == Zero:
    result = "0"
  elif a == low(Int128):
    result = "-170141183460469231731687303715884105728"
  else:
    let isNegative = isNegative(a)
    var a = abs(a)
    while a > Zero:
      let (quot, rem) = divMod(a, Ten)
      result.add "0123456789"[rem.toInt64]
      a = quot
    if isNegative:
      result.add '-'

    var i = 0
    var j = high(result)
    while i < j:
      swap(result[i], result[j])
      i += 1
      j -= 1

proc parseDecimalInt128*(arg: string, pos: int = 0): Int128 =
  assert(pos < arg.len)
  assert(arg[pos] in {'-','0'..'9'})

  var isNegative = false
  var pos = pos
  if arg[pos] == '-':
    isNegative = true
    pos += 1

  result = Zero
  while pos < arg.len and arg[pos] in '0' .. '9':
    result = result * Ten
    result.inc(uint32(arg[pos]) - uint32('0'))
    pos += 1

  if isNegative:
    result = -result

# fluff

proc `<`*(a: Int128, b: BiggestInt): bool =
  cmp(a,toInt128(b)) < 0

proc `<`*(a: BiggestInt, b: Int128): bool =
  cmp(toInt128(a), b) < 0

proc `<=`*(a: Int128, b: BiggestInt): bool =
  cmp(a,toInt128(b)) <= 0

proc `<=`*(a: BiggestInt, b: Int128): bool =
  cmp(toInt128(a), b) <= 0

proc `==`*(a: Int128, b: BiggestInt): bool =
  a == toInt128(b)

proc `==`*(a: BiggestInt, b: Int128): bool =
  toInt128(a) == b

proc `-`*(a: BiggestInt, b: Int128): Int128 =
  toInt128(a) - b

proc `-`*(a: Int128, b: BiggestInt): Int128 =
  a - toInt128(b)

proc `+`*(a: BiggestInt, b: Int128): Int128 =
  toInt128(a) + b

proc `+`*(a: Int128, b: BiggestInt): Int128 =
  a + toInt128(b)


when isMainModule:
  let (a,b) = divMod(Ten,Ten)

  doAssert $One == "1"
  doAssert $Ten == "10"
  doAssert $Zero == "0"
  let c = parseDecimalInt128("12345678989876543210123456789")
  doAssert $c == "12345678989876543210123456789"

  var d : array[39, Int128]
  d[0] =  parseDecimalInt128("1")
  d[1] =  parseDecimalInt128("10")
  d[2] =  parseDecimalInt128("100")
  d[3] =  parseDecimalInt128("1000")
  d[4] =  parseDecimalInt128("10000")
  d[5] =  parseDecimalInt128("100000")
  d[6] =  parseDecimalInt128("1000000")
  d[7] =  parseDecimalInt128("10000000")
  d[8] =  parseDecimalInt128("100000000")
  d[9] =  parseDecimalInt128("1000000000")
  d[10] = parseDecimalInt128("10000000000")
  d[11] = parseDecimalInt128("100000000000")
  d[12] = parseDecimalInt128("1000000000000")
  d[13] = parseDecimalInt128("10000000000000")
  d[14] = parseDecimalInt128("100000000000000")
  d[15] = parseDecimalInt128("1000000000000000")
  d[16] = parseDecimalInt128("10000000000000000")
  d[17] = parseDecimalInt128("100000000000000000")
  d[18] = parseDecimalInt128("1000000000000000000")
  d[19] = parseDecimalInt128("10000000000000000000")
  d[20] = parseDecimalInt128("100000000000000000000")
  d[21] = parseDecimalInt128("1000000000000000000000")
  d[22] = parseDecimalInt128("10000000000000000000000")
  d[23] = parseDecimalInt128("100000000000000000000000")
  d[24] = parseDecimalInt128("1000000000000000000000000")
  d[25] = parseDecimalInt128("10000000000000000000000000")
  d[26] = parseDecimalInt128("100000000000000000000000000")
  d[27] = parseDecimalInt128("1000000000000000000000000000")
  d[28] = parseDecimalInt128("10000000000000000000000000000")
  d[29] = parseDecimalInt128("100000000000000000000000000000")
  d[30] = parseDecimalInt128("1000000000000000000000000000000")
  d[31] = parseDecimalInt128("10000000000000000000000000000000")
  d[32] = parseDecimalInt128("100000000000000000000000000000000")
  d[33] = parseDecimalInt128("1000000000000000000000000000000000")
  d[34] = parseDecimalInt128("10000000000000000000000000000000000")
  d[35] = parseDecimalInt128("100000000000000000000000000000000000")
  d[36] = parseDecimalInt128("1000000000000000000000000000000000000")
  d[37] = parseDecimalInt128("10000000000000000000000000000000000000")
  d[38] = parseDecimalInt128("100000000000000000000000000000000000000")

  for i in 0 ..< d.len:
    for j in 0 ..< d.len:
      doAssert(cmp(d[i], d[j]) == cmp(i,j))
      if i + j < d.len:
        doAssert d[i] * d[j] == d[i+j]
      if i - j >= 0:
        doAssert d[i] div d[j] == d[i-j]

  var sum: Int128

  for it in d:
    sum += it

  doAssert $sum == "111111111111111111111111111111111111111"

  for it in d.mitems:
    it = -it

  for i in 0 ..< d.len:
    for j in 0 ..< d.len:
      doAssert(cmp(d[i], d[j]) == -cmp(i,j))
      if i + j < d.len:
        doAssert d[i] * d[j] == -d[i+j]
      if i - j >= 0:
        doAssert d[i] div d[j] == -d[i-j]

  doAssert $high(Int128) == "170141183460469231731687303715884105727"
  doAssert $low(Int128) == "-170141183460469231731687303715884105728"
