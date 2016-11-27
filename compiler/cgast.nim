#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## The subset of the Nim Ast that is produced.

import macros
from msgs import TLineInfo, localError
import ast, idents

const
  nkCurlyBlock* = nkStmtList #  {child; child-2; ...; child-N}
  nkDecl* = nkCommand # child child-2 child-3  # children simply concat
  nkVerbatim* = nkStrLit # node used for its string field, but don't escape
                      # the string. It is already escaped.
  nkProcHeader* = nkProcDef # we share proc headers for both forward decls
                            # and full C function declarations to safe space.
  nkSemiList* = nkArgList # semicolon separated list (used for proc forwardings)
  nkUnion* = nkRefTy

# A full proc looks like this:  nkDecl(nkProcHeader(...), nkCurlyBlock(...))
const
  nfIsTemp* = nfBase2
  nkIsData* = nfBase8

when false:
  nfBase16 nfAllConst,
    nfTransf,
    nfNoRewrite,
    nfSem,
    nfLL,
    nfDotField,
    nfDotSetter,
    nfExplicitCall,
    nfExprCall,
    nfIsRef,
    nfPreventCg

type
  Writer* = object
    f: File
    indent: int

template writeCgAst(w: var Writer; s: string) =
  w.f.write s

proc wrInd(w: var Writer) =
  w.f.write '\L'
  for i in 1..w.indent*2:
    w.f.write ' '

macro wr(x: varargs[untyped]): untyped =
  result = newStmtList()
  for a in x:
    if a.eqIdent"ind": result.add newCall(newIdentNode"wrInd", newIdentNode"w")
    else: result.add newCall(newIdentNode"writeCgAst", newIdentNode"w", a)

macro wrs(s: static[string]): untyped =
  var i = 0
  while i < s.len: discard

proc writeCgAst(w: var Writer; n: PNode) =
  template loopSep(sep: string; start = 0) =
    for i in start..<n.len:
      if i > start: wr sep
      wr n[i]

  template indSep(start = 0) =
    for i in start..<n.len:
      wr ind, n[i]

  template ind2Sep(start = 0) =
    inc w.indent
    indSep(start)
    dec w.indent

  case n.kind
  of nkEmpty: discard
  of nkCurlyBlock:
    wr "{"
    inc w.indent
    for i in 0..<n.len:
      wr ind, n[i], ";"
    dec w.indent
    wr "\L}\L"
  of nkCurly:
    wr "{"
    loopSep ", "
    wr "}"
  of nkDecl:
    # int const register x # usually last child is the important
    loopSep " "
  of nkSemiList:
    for i in 0..<n.len:
      wr "\L", n[i], ";"
    wr "\L"
  of nkVerbatim: wr n.strVal
  of nkSym: wr n.sym.cg
  of nkPar:
    wr "("
    loopSep ", "
    wr ")"
  of nkCall:
    wr n[0], "("
    loopSep ", ", 1
    wr ")"
  of nkInfix: wr "(", n[1], " ", n[0], " ", n[2], ")"
  of nkPrefix: wr n[0], "(", n[1], ")"
  of nkPostfix: wr "(", n[1], ")", n[0]
  of nkAsgn: wr n[0], " = ", n[1]
  of nkAddr:
    if n[0].kind == nkDerefExpr:
      wr "(", n[0], ")"
    else:
      wr "&(", n[0], ")"
  of nkDerefExpr:
    if n[0].kind == nkAddr:
      wr "(", n[0], ")"
    else:
      wr "*(", n[0], ")"
  of nkDotExpr:
    if n[0].kind == nkDerefExpr:
      wr n[0][0], "->", n[1]
    else:
      wr n[0], ".", n[1]
  of nkBracketExpr: wr n[0], "[", n[1], "]"
  of nkCaseStmt:
    wr "switch (", n[0], ") {"
    ind2Sep 1
    wr ind, "}\L"
  of nkOfBranch:
    if n.len > 1:
      wr "case "
      for i in 0..n.len-2:
        wr n[i], ": "
    else:
      wr "default: "
    let stmts = n[n.len-1]
    if stmts.kind == nkCurlyBlock:
      wr stmts, " break;\L"
    else:
      wr "{"
      inc w.indent
      wr ind, stmts, "} break;\L"
      dec w.indent
  of nkGotoState: wr "goto ", n[0]
  of nkState: wr n[0], ": ;"
  of nkWhileStmt: wr "while (", n[0], ") ", n[1]
  of nkIfStmt:
    wr "if (", n[0], ") ", n[1]
    indSep 2
  of nkElifBranch: wr "else if (", n[0], ") ", n[1]
  of nkElse: wr "else ", n[0]
  of nkIfExpr: wr "((", n[0], ")? (", n[1], ") : (", n[2], "))"
  of nkTypeDef: wr "\Ltypedef ", n[0], " ", n[1]
  of nkProcDef: wr "\L", n[0], " ", n[1], " ", n[2], n[3]
  of nkObjectTy:
    wr "struct ", n[0], "{"
    ind2Sep 1
    wr "\L}\L"
  of nkUnion:
    wr "union ", n[0], "{"
    ind2Sep 1
    wr "\L}\L"
  of nkOfInherit: wr n[0], ": ", n[1]
  of nkPtrTy: wr n[0], "*"
  of nkVarTy: wr n[0], "&"
  else: localError n.info, "codegen produced an unsupported node"

proc writeCgAst*(filename: string; n: PNode) =
  var w: Writer
  w.f = open(filename, fmWrite, 8*1024)
  writeCgAst(w, n)
  w.f.close()

proc atom*(s: string): PNode =
  result = newStrNode(nkVerbatim, s)

proc atom*(i: BiggestInt): PNode =
  result = newStrNode(nkVerbatim, $i)

proc atom*(s: string; typ: PType): PNode =
  result = newStrNode(nkVerbatim, s)
  result.typ = typ

when false:
  proc track*(result, origin: PNode) {.inline.} =
    result.typ = origin.typ
    result.info = origin.info

proc newDotExpr*(a, b: PNode): PNode =
  result = newNodeI(nkDotExpr, a.info, 2)
  result.sons[0] = a
  result.sons[1] = b

proc tca(n: NimNode): NimNode =
  case n.kind
  of nnkIdent, nnkIntLit:
    result = newCall(bindSym"atom", newLit(repr n))
  of nnkDotExpr, nnkBracketExpr, nnkCall, nnkCommand, nnkPrefix, nnkInfix:
    result = newCall(bindSym"newTree", ident(($n.kind).substr(1)))
    for i in 0..<n.len:
      result.add tca n[i]
  of nnkAccQuoted:
    expectLen n, 1
    result = n[0]
  of nnkPar:
    expectLen n, 1
    result = newCall(bindSym"newTree", bindSym"nkPar", tca n[0])
  else:
    error "cannot map to AST construction", n

macro tc*(x: untyped): untyped =
  ## General tree construction macro for convenience.
  result = tca x

when isMainModule:
  let tt = newTree(nkCurlyBlock, newTree(nkAsgn,
    newStrNode(nkVerbatim, "x"), newStrNode(nkVerbatim, "y")),
    newTree(nkAsgn,
      newStrNode(nkVerbatim, "x"), newStrNode(nkVerbatim, "y")))
  writeCgAst("testor.c", tt)

