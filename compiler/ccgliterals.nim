#
#
#           The Nim Compiler
#        (c) Copyright 2018 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from cgen.nim

## This include file contains the logic to produce constant string
## and seq literals. The code here is responsible that
## ``const x = ["a", "b"]`` works without hidden runtime creation code.
## The price is that seqs and strings are not purely a library
## implementation.

template detectVersion(field, corename) =
  if m.g.field == 0:
    let core = getCompilerProc(m.g.graph, corename)
    if core == nil or core.kind != skConst:
      m.g.field = 1
    else:
      m.g.field = toInt(ast.getInt(core.ast))
  result = m.g.field

proc detectStrVersion(m: BModule): int =
  detectVersion(strVersion, "nimStrVersion")

proc detectSeqVersion(m: BModule): int =
  detectVersion(seqVersion, "nimSeqVersion")

# ----- Version 1: GC'ed strings and seqs --------------------------------

proc genStringLiteralDataOnlyV1(m: BModule, s: string): Rope =
  discard cgsym(m, "TGenericSeq")
  result = getTempName(m)
  addf(m.s[cfsData], "STRING_LITERAL($1, $2, $3);$n",
       [result, makeCString(s), rope(len(s))])

proc genStringLiteralV1(m: BModule; n: PNode): Rope =
  if s.isNil:
    result = ropecg(m, "((#NimStringDesc*) NIM_NIL)", [])
  else:
    let id = nodeTableTestOrSet(m.dataCache, n, m.labels)
    if id == m.labels:
      # string literal not found in the cache:
      result = ropecg(m, "((#NimStringDesc*) &$1)",
                      [genStringLiteralDataOnlyV1(m, n.strVal)])
    else:
      result = ropecg(m, "((#NimStringDesc*) &$1$2)",
                      [m.tmpBase, id])

# ------ Version 2: destructor based strings and seqs -----------------------

proc genStringLiteralDataOnlyV2(m: BModule, s: string; result: Rope) =
  addf(m.s[cfsData], "static const struct {$n" &
       "  NI cap; void* allocator; NIM_CHAR data[$2+1];$n" &
       "} $1 = { $2, NIM_NIL, $3 };$n",
       [result, rope(len(s)), makeCString(s)])

proc genStringLiteralV2(m: BModule; n: PNode): Rope =
  let id = nodeTableTestOrSet(m.dataCache, n, m.labels)
  if id == m.labels:
    let pureLit = getTempName(m)
    genStringLiteralDataOnlyV2(m, n.strVal, pureLit)
    result = getTempName(m)
    discard cgsym(m, "NimStrPayload")
    discard cgsym(m, "NimStringV2")
    # string literal not found in the cache:
    addf(m.s[cfsData], "static const NimStringV2 $1 = {$2, (NimStrPayload*)&$3};$n",
          [result, rope(len(n.strVal)), pureLit])
  else:
    result = getTempName(m)
    addf(m.s[cfsData], "static const NimStringV2 $1 = {$2, (NimStrPayload*)&$3};$n",
          [result, rope(len(n.strVal)), m.tmpBase & rope(id)])

proc genStringLiteralV2Const(m: BModule; n: PNode): Rope =
  let id = nodeTableTestOrSet(m.dataCache, n, m.labels)
  var pureLit: Rope
  if id == m.labels:
    pureLit = getTempName(m)
    discard cgsym(m, "NimStrPayload")
    discard cgsym(m, "NimStringV2")
    # string literal not found in the cache:
    genStringLiteralDataOnlyV2(m, n.strVal, pureLit)
  else:
    pureLit = m.tmpBase & rope(id)
  result = "{$1, (NimStrPayload*)&$2}" % [rope(len(n.strVal)), pureLit]

# ------ Version selector ---------------------------------------------------

proc genStringLiteralDataOnly(m: BModule; s: string; info: TLineInfo): Rope =
  case detectStrVersion(m)
  of 0, 1: result = genStringLiteralDataOnlyV1(m, s)
  of 2:
    result = getTempName(m)
    genStringLiteralDataOnlyV2(m, s, result)
  else:
    localError(m.config, info, "cannot determine how to produce code for string literal")

proc genNilStringLiteral(m: BModule; info: TLineInfo): Rope =
  result = ropecg(m, "((#NimStringDesc*) NIM_NIL)", [])

proc genStringLiteral(m: BModule; n: PNode): Rope =
  case detectStrVersion(m)
  of 0, 1: result = genStringLiteralV1(m, n)
  of 2: result = genStringLiteralV2(m, n)
  else:
    localError(m.config, n.info, "cannot determine how to produce code for string literal")
