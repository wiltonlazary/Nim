#
#
#           The Nim Compiler
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements the '.liftLocals' pragma.

import
  intsets, strutils, options, ast, astalgo, msgs,
  idents, renderer, types, lowerings

from pragmas import getPragmaVal
from wordrecg import wLiftLocals

type
  Ctx = object
    partialParam: PSym
    objType: PType

proc interestingVar(s: PSym): bool {.inline.} =
  result = s.kind in {skVar, skLet, skTemp, skForVar, skResult} and
    sfGlobal notin s.flags

proc lookupOrAdd(c: var Ctx; s: PSym; info: TLineInfo): PNode =
  let field = addUniqueField(c.objType, s)
  var deref = newNodeI(nkHiddenDeref, info)
  deref.typ = c.objType
  add(deref, newSymNode(c.partialParam, info))
  result = newNodeI(nkDotExpr, info)
  add(result, deref)
  add(result, newSymNode(field))
  result.typ = field.typ

proc liftLocals(n: PNode; i: int; c: var Ctx) =
  let it = n[i]
  case it.kind
  of nkSym:
    if interestingVar(it.sym):
      n[i] = lookupOrAdd(c, it.sym, it.info)
  of procDefs, nkTypeSection: discard
  else:
    for i in 0 ..< it.safeLen:
      liftLocals(it, i, c)

proc lookupParam(params, dest: PNode): PSym =
  if dest.kind != nkIdent: return nil
  for i in 1 ..< params.len:
    if params[i].kind == nkSym and params[i].sym.name.id == dest.ident.id:
      return params[i].sym

proc liftLocalsIfRequested*(prc: PSym; n: PNode): PNode =
  let liftDest = getPragmaVal(prc.ast, wLiftLocals)
  if liftDest == nil: return n
  let partialParam = lookupParam(prc.typ.n, liftDest)
  if partialParam.isNil:
    localError(liftDest.info, "'$1' is not a parameter of '$2'" %
              [$liftDest, prc.name.s])
    return n
  let objType = partialParam.typ.skipTypes(abstractPtrs)
  if objType.kind != tyObject or tfPartial notin objType.flags:
    localError(liftDest.info, "parameter '$1' is not a pointer to a partial object" % $liftDest)
    return n
  var c = Ctx(partialParam: partialParam, objType: objType)
  let w = newTree(nkStmtList, n)
  liftLocals(w, 0, c)
  result = w[0]
