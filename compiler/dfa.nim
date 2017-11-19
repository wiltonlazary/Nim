#
#
#           The Nim Compiler
#        (c) Copyright 2017 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Data flow analysis for Nim. For now the task is to prove that every
## usage of a local variable 'v' is covered by an initialization to 'v'
## first.
## We transform the AST into a linear list of instructions first to
## make this easier to handle: There are only 2 different branching
## instructions: 'goto X' is an unconditional goto, 'fork X'
## is a conditional goto (either the next instruction or 'X' can be
## taken). Exhaustive case statements are translated
## so that the last branch is transformed into an 'else' branch.
## ``return`` and ``break`` are all covered by 'goto'.
## The case to detect is ``use v`` that is not dominated by
## a ``def v``.
## The data structures and algorithms used here are inspired by
## "A Graph–Free Approach to Data–Flow Analysis" by Markus Mohnen.
## https://link.springer.com/content/pdf/10.1007/3-540-45937-5_6.pdf

import ast, astalgo, types, intsets, tables, msgs

type
  InstrKind* = enum
    goto, fork, def, use,
    useWithinCall # this strange special case is used to get more
                  # move optimizations out of regular code
                  # XXX This is still overly pessimistic in
                  # call(let x = foo; bar(x))
  Instr* = object
    n*: PNode
    case kind*: InstrKind
    of def, use, useWithinCall: sym*: PSym
    of goto, fork: dest*: int

  ControlFlowGraph* = seq[Instr]

  TPosition = distinct int
  TBlock = object
    label: PSym
    fixups: seq[TPosition]

  ValueKind = enum
    undef, value, valueOrUndef

  Con = object
    code: ControlFlowGraph
    inCall: int
    blocks: seq[TBlock]

proc debugInfo(info: TLineInfo): string =
  result = info.toFilename & ":" & $info.line

proc codeListing(c: ControlFlowGraph, result: var string, start=0; last = -1) =
  # for debugging purposes
  # first iteration: compute all necessary labels:
  var jumpTargets = initIntSet()
  let last = if last < 0: c.len-1 else: min(last, c.len-1)
  for i in start..last:
    if c[i].kind in {goto, fork}:
      jumpTargets.incl(i+c[i].dest)
  var i = start
  while i <= last:
    if i in jumpTargets: result.add("L" & $i & ":\n")
    result.add "\t"
    result.add $c[i].kind
    result.add "\t"
    case c[i].kind
    of def, use, useWithinCall:
      result.add c[i].sym.name.s
    of goto, fork:
      result.add "L"
      result.add c[i].dest+i
    result.add("\t#")
    result.add(debugInfo(c[i].n.info))
    result.add("\n")
    inc i
  if i in jumpTargets: result.add("L" & $i & ": End\n")


proc echoCfg*(c: ControlFlowGraph; start=0; last = -1) {.deprecated.} =
  ## echos the ControlFlowGraph for debugging purposes.
  var buf = ""
  codeListing(c, buf, start, last)
  echo buf

proc forkI(c: var Con; n: PNode): TPosition =
  result = TPosition(c.code.len)
  c.code.add Instr(n: n, kind: fork, dest: 0)

proc gotoI(c: var Con; n: PNode): TPosition =
  result = TPosition(c.code.len)
  c.code.add Instr(n: n, kind: goto, dest: 0)

proc genLabel(c: Con): TPosition =
  result = TPosition(c.code.len)

proc jmpBack(c: var Con, n: PNode, p = TPosition(0)) =
  let dist = p.int - c.code.len
  internalAssert(-0x7fff < dist and dist < 0x7fff)
  c.code.add Instr(n: n, kind: goto, dest: dist)

proc patch(c: var Con, p: TPosition) =
  # patch with current index
  let p = p.int
  let diff = c.code.len - p
  internalAssert(-0x7fff < diff and diff < 0x7fff)
  c.code[p].dest = diff

proc popBlock(c: var Con; oldLen: int) =
  for f in c.blocks[oldLen].fixups:
    c.patch(f)
  c.blocks.setLen(oldLen)

template withBlock(labl: PSym; body: untyped) {.dirty.} =
  var oldLen {.gensym.} = c.blocks.len
  c.blocks.add TBlock(label: labl, fixups: @[])
  body
  popBlock(c, oldLen)

proc isTrue(n: PNode): bool =
  n.kind == nkSym and n.sym.kind == skEnumField and n.sym.position != 0 or
    n.kind == nkIntLit and n.intVal != 0

proc gen(c: var Con; n: PNode) # {.noSideEffect.}

proc genWhile(c: var Con; n: PNode) =
  # L1:
  #   cond, tmp
  #   fjmp tmp, L2
  #   body
  #   jmp L1
  # L2:
  let L1 = c.genLabel
  withBlock(nil):
    if isTrue(n.sons[0]):
      c.gen(n.sons[1])
      c.jmpBack(n, L1)
    else:
      c.gen(n.sons[0])
      let L2 = c.forkI(n)
      c.gen(n.sons[1])
      c.jmpBack(n, L1)
      c.patch(L2)

proc genBlock(c: var Con; n: PNode) =
  withBlock(n.sons[0].sym):
    c.gen(n.sons[1])

proc genBreak(c: var Con; n: PNode) =
  let L1 = c.gotoI(n)
  if n.sons[0].kind == nkSym:
    #echo cast[int](n.sons[0].sym)
    for i in countdown(c.blocks.len-1, 0):
      if c.blocks[i].label == n.sons[0].sym:
        c.blocks[i].fixups.add L1
        return
    globalError(n.info, errGenerated, "VM problem: cannot find 'break' target")
  else:
    c.blocks[c.blocks.high].fixups.add L1

proc genIf(c: var Con, n: PNode) =
  var endings: seq[TPosition] = @[]
  for i in countup(0, len(n) - 1):
    var it = n.sons[i]
    if it.len == 2:
      c.gen(it.sons[0].sons[1])
      var elsePos = c.forkI(it.sons[0].sons[1])
      c.gen(it.sons[1])
      if i < sonsLen(n)-1:
        endings.add(c.gotoI(it.sons[1]))
      c.patch(elsePos)
    else:
      c.gen(it.sons[0])
  for endPos in endings: c.patch(endPos)

proc genAndOr(c: var Con; n: PNode) =
  #   asgn dest, a
  #   fork L1
  #   asgn dest, b
  # L1:
  c.gen(n.sons[1])
  let L1 = c.forkI(n)
  c.gen(n.sons[2])
  c.patch(L1)

proc genCase(c: var Con; n: PNode) =
  #  if (!expr1) goto L1;
  #    thenPart
  #    goto LEnd
  #  L1:
  #  if (!expr2) goto L2;
  #    thenPart2
  #    goto LEnd
  #  L2:
  #    elsePart
  #  Lend:
  var endings: seq[TPosition] = @[]
  c.gen(n.sons[0])
  for i in 1 ..< n.len:
    let it = n.sons[i]
    if it.len == 1:
      c.gen(it.sons[0])
    else:
      let elsePos = c.forkI(it.lastSon)
      c.gen(it.lastSon)
      if i < sonsLen(n)-1:
        endings.add(c.gotoI(it.lastSon))
      c.patch(elsePos)
  for endPos in endings: c.patch(endPos)

proc genTry(c: var Con; n: PNode) =
  var endings: seq[TPosition] = @[]
  let elsePos = c.forkI(n)
  c.gen(n.sons[0])
  c.patch(elsePos)
  for i in 1 ..< n.len:
    let it = n.sons[i]
    if it.kind != nkFinally:
      var blen = len(it)
      let endExcept = c.forkI(it)
      c.gen(it.lastSon)
      if i < sonsLen(n)-1:
        endings.add(c.gotoI(it))
      c.patch(endExcept)
  for endPos in endings: c.patch(endPos)
  let fin = lastSon(n)
  if fin.kind == nkFinally:
    c.gen(fin.sons[0])

proc genRaise(c: var Con; n: PNode) =
  gen(c, n.sons[0])
  c.code.add Instr(n: n, kind: goto, dest: high(int) - c.code.len)

proc genReturn(c: var Con; n: PNode) =
  if n.sons[0].kind != nkEmpty: gen(c, n.sons[0])
  c.code.add Instr(n: n, kind: goto, dest: high(int) - c.code.len)

const
  InterestingSyms = {skVar, skResult, skLet}

proc genUse(c: var Con; n: PNode) =
  var n = n
  while n.kind in {nkDotExpr, nkCheckedFieldExpr,
                   nkBracketExpr, nkDerefExpr, nkHiddenDeref,
                   nkAddr, nkHiddenAddr}:
    n = n[0]
  if n.kind == nkSym and n.sym.kind in InterestingSyms:
    if c.inCall > 0:
      c.code.add Instr(n: n, kind: useWithinCall, sym: n.sym)
    else:
      c.code.add Instr(n: n, kind: use, sym: n.sym)

proc genDef(c: var Con; n: PNode) =
  if n.kind == nkSym and n.sym.kind in InterestingSyms:
    c.code.add Instr(n: n, kind: def, sym: n.sym)

proc genCall(c: var Con; n: PNode) =
  gen(c, n[0])
  var t = n[0].typ
  if t != nil: t = t.skipTypes(abstractInst)
  inc c.inCall
  for i in 1..<n.len:
    gen(c, n[i])
    if t != nil and i < t.len and t.sons[i].kind == tyVar:
      genDef(c, n[i])
  dec c.inCall

proc genMagic(c: var Con; n: PNode; m: TMagic) =
  case m
  of mAnd, mOr: c.genAndOr(n)
  of mNew, mNewFinalize:
    genDef(c, n[1])
    for i in 2..<n.len: gen(c, n[i])
  of mExit:
    genCall(c, n)
    c.code.add Instr(n: n, kind: goto, dest: high(int) - c.code.len)
  else:
    genCall(c, n)

proc genVarSection(c: var Con; n: PNode) =
  for a in n:
    if a.kind == nkCommentStmt: continue
    if a.kind == nkVarTuple:
      gen(c, a.lastSon)
      for i in 0 .. a.len-3: genDef(c, a[i])
    else:
      gen(c, a.lastSon)
      if a.lastSon.kind != nkEmpty:
        genDef(c, a.sons[0])

proc gen(c: var Con; n: PNode) =
  case n.kind
  of nkSym: genUse(c, n)
  of nkCallKinds:
    if n.sons[0].kind == nkSym:
      let s = n.sons[0].sym
      if s.magic != mNone:
        genMagic(c, n, s.magic)
      else:
        genCall(c, n)
    else:
      genCall(c, n)
  of nkCharLit..nkNilLit: discard
  of nkAsgn, nkFastAsgn:
    gen(c, n[1])
    genDef(c, n[0])
  of nkDotExpr, nkCheckedFieldExpr, nkBracketExpr,
     nkDerefExpr, nkHiddenDeref, nkAddr, nkHiddenAddr:
    gen(c, n[0])
  of nkIfStmt, nkIfExpr: genIf(c, n)
  of nkWhenStmt:
    # This is "when nimvm" node. Chose the first branch.
    gen(c, n.sons[0].sons[1])
  of nkCaseStmt: genCase(c, n)
  of nkWhileStmt: genWhile(c, n)
  of nkBlockExpr, nkBlockStmt: genBlock(c, n)
  of nkReturnStmt: genReturn(c, n)
  of nkRaiseStmt: genRaise(c, n)
  of nkBreakStmt: genBreak(c, n)
  of nkTryStmt: genTry(c, n)
  of nkStmtList, nkStmtListExpr, nkChckRangeF, nkChckRange64, nkChckRange,
     nkBracket, nkCurly, nkPar, nkClosure, nkObjConstr:
    for x in n: gen(c, x)
  of nkPragmaBlock: gen(c, n.lastSon)
  of nkDiscardStmt: gen(c, n.sons[0])
  of nkHiddenStdConv, nkHiddenSubConv, nkConv, nkExprColonExpr, nkExprEqExpr,
     nkCast:
    gen(c, n.sons[1])
  of nkObjDownConv, nkStringToCString, nkCStringToString: gen(c, n.sons[0])
  of nkVarSection, nkLetSection: genVarSection(c, n)
  else: discard

proc dfa(code: seq[Instr]) =
  # We aggressively push 'undef' values for every 'use v' instruction
  # until they are eliminated via a 'def v' instructions.
  # If we manage to push one 'undef' to a 'use' instruction, we produce
  # an error:
  var undef = initIntSet()
  for i in 0..<code.len:
    if code[i].kind == use: undef.incl(code[i].sym.id)

  var s = newSeq[IntSet](code.len)
  for i in 0..<code.len:
    assign(s[i], undef)

  # In the original paper, W := {0,...,n} is done. This is wasteful, we
  # have no intention to analyse a program like
  #
  # return 3
  # echo a + b
  #
  # any further than necessary.
  var w = @[0]
  while w.len > 0:
    var pc = w[^1]
    # this simulates a single linear control flow execution:
    while true:
      # according to the paper, it is better to shrink the working set here
      # in this inner loop:
      let widx = w.find(pc)
      if widx >= 0: w.del(widx)
      # our interpretation ![I!]:
      var sid = -1
      case code[pc].kind
      of goto, fork: discard
      of use, useWithinCall:
        let sym = code[pc].sym
        if s[pc].contains(sym.id):
          localError(code[pc].n.info, "variable read before initialized: " & sym.name.s)
      of def:
        sid = code[pc].sym.id

      var pc2: int
      if code[pc].kind == goto:
        pc2 = pc + code[pc].dest
      else:
        pc2 = pc + 1
        if code[pc].kind == fork:
          let l = pc + code[pc].dest
          if sid >= 0 and s[l].missingOrExcl(sid):
            w.add l

      if sid >= 0 and s[pc2].missingOrExcl(sid):
        pc = pc2
      else:
        break
      if pc >= code.len: break

    when false:
      case code[pc].kind
      of use:
        let s = code[pc].sym
        if undefB.contains(s.id):
          localError(code[pc].n.info, "variable read before initialized: " & s.name.s)
          break
        inc pc
      of def:
        let s = code[pc].sym
        # exclude 'undef' for s for this path through the graph.
        if not undefB.missingOrExcl(s.id):
          inc pc
        else:
          break
        #undefB.excl s.id
        #inc pc
        when false:
          let prev = bindings.getOrDefault(s.id)
          if prev != value:
            # well now it has a value and we made progress, so
            bindings[s.id] = value
            inc pc
          else:
            break
      of fork:
        let diff = code[pc].dest
        # we follow pc + 1 and remember the label for later:
        w.add pc+diff
        inc pc
      of goto:
        let diff = code[pc].dest
        pc = pc + diff
      if pc >= code.len: break

proc dataflowAnalysis*(s: PSym; body: PNode) =
  var c = Con(code: @[], blocks: @[])
  gen(c, body)
  #echoCfg(c.code)
  dfa(c.code)

proc constructCfg*(s: PSym; body: PNode): ControlFlowGraph =
  ## constructs a control flow graph for ``body``.
  var c = Con(code: @[], blocks: @[])
  shallowCopy(result, c.code)
