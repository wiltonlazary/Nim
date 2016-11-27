#
#
#           The Nim Compiler
#        (c) Copyright 2016 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from cgen.nim

# ------------------------- Name Mangling --------------------------------

import sighashes

proc isKeyword(w: PIdent): bool =
  # Nim and C++ share some keywords
  # it's more efficient to test the whole Nim keywords range
  case w.id
  of ccgKeywordsLow..ccgKeywordsHigh,
     nimKeywordsLow..nimKeywordsHigh,
     ord(wInline): return true
  else: return false

proc mangleField(name: PIdent): string =
  result = mangle(name.s)
  if isKeyword(name):
    result[0] = result[0].toUpperAscii
    # Mangling makes everything lowercase,
    # but some identifiers are C keywords

when false:
  proc hashOwner(s: PSym): SigHash =
    var m = s
    while m.kind != skModule: m = m.owner
    let p = m.owner
    assert p.kind == skPackage
    result = gDebugInfo.register(p.name.s, m.name.s)

proc idOrSig(m: BModule; s: PSym): string =
  if s.kind in routineKinds and s.typ != nil and sfExported in s.flags and
     s.typ.callConv != ccInline:
    # signatures for exported routines are reliable enough to
    # produce a unique name and this means produced C++ is more stable wrt
    # Nim changes:
    result = $hashProc(s)
  else:
    result = "_" & $s.id

proc mangleName(m: BModule; s: PSym): PNode =
  result = s.cg
  if result == nil:
    let keepOrigName = s.kind in skLocalVars - {skForVar} and
      {sfFromGeneric, sfGlobal, sfShadowed, sfGenSym} * s.flags == {} and
      not isKeyword(s.name)
    # Even with all these inefficient checks, the bootstrap
    # time is actually improved. This is probably because so many
    # rope concatenations are now eliminated.
    #
    # sfFromGeneric is needed in order to avoid multiple
    # definitions of certain variables generated in transf with
    # names such as:
    # `r`, `res`
    # I need to study where these come from.
    #
    # about sfShadowed:
    # consider the following Nim code:
    #   var x = 10
    #   block:
    #     var x = something(x)
    # The generated C code will be:
    #   NI x;
    #   x = 10;
    #   {
    #     NI x;
    #     x = something(x); // Oops, x is already shadowed here
    #   }
    # Right now, we work-around by not keeping the original name
    # of the shadowed variable, but we can do better - we can
    # create an alternative reference to it in the outer scope and
    # use that in the inner scope.
    #
    # about isCKeyword:
    # Nim variable names can be C keywords.
    # We need to avoid such names in the generated code.
    #
    # about sfGlobal:
    # This seems to be harder - a top level extern variable from
    # another modules can have the same name as a local one.
    # Maybe we should just implement sfShadowed for them too.
    #
    # about skForVar:
    # These are not properly scoped now - we need to add blocks
    # around for loops in transf
    var str = s.name.s.mangle
    if keepOrigName:
      str.add "0"
    else:
      str.add m.idOrSig(s)
    result = atom(str)
    s.cg = result

proc typeName(typ: PType): string =
  result = if typ.sym != nil: typ.sym.name.s.mangle
           else: "TY"

proc getTypeName(m: BModule; typ: PType; sig: SigHash): PNode =
  let typ = if typ.kind == tyAlias: typ.lastSon else: typ
  if typ.sym != nil and {sfImportc, sfExportc} * typ.sym.flags != {}:
    result = typ.sym.cg
  else:
    if typ.cg == nil:
      typ.cg = atom(typ.typeName & $sig)
    else:
      when defined(debugSigHashes):
        # check consistency:
        assert($typ.cg == $(typ.typeName & $sig))
    result = typ.cg
  if result == nil: internalError("getTypeName: " & $typ.kind)

proc mapSetType(typ: PType): TCTypeKind =
  case int(getSize(typ))
  of 1: result = ctInt8
  of 2: result = ctInt16
  of 4: result = ctInt32
  of 8: result = ctInt64
  else: result = ctArray

proc mapType(typ: PType): TCTypeKind =
  ## Maps a Nim type to a C type
  case typ.kind
  of tyNone, tyStmt: result = ctVoid
  of tyBool: result = ctBool
  of tyChar: result = ctChar
  of tySet: result = mapSetType(typ)
  of tyOpenArray, tyArray, tyVarargs: result = ctArray
  of tyObject, tyTuple: result = ctStruct
  of tyGenericBody, tyGenericInst, tyGenericParam, tyDistinct, tyOrdinal,
     tyTypeDesc, tyAlias:
    result = mapType(lastSon(typ))
  of tyEnum:
    if firstOrd(typ) < 0:
      result = ctInt32
    else:
      case int(getSize(typ))
      of 1: result = ctUInt8
      of 2: result = ctUInt16
      of 4: result = ctInt32
      of 8: result = ctInt64
      else: internalError("mapType")
  of tyRange: result = mapType(typ.sons[0])
  of tyPtr, tyVar, tyRef:
    var base = skipTypes(typ.lastSon, typedescInst)
    case base.kind
    of tyOpenArray, tyArray, tyVarargs: result = ctPtrToArray
    #of tySet:
    #  if mapSetType(base) == ctArray: result = ctPtrToArray
    #  else: result = ctPtr
    # XXX for some reason this breaks the pegs module
    else: result = ctPtr
  of tyPointer: result = ctPtr
  of tySequence: result = ctNimSeq
  of tyProc: result = if typ.callConv != ccClosure: ctProc else: ctStruct
  of tyString: result = ctNimStr
  of tyCString: result = ctCString
  of tyInt..tyUInt64:
    result = TCTypeKind(ord(typ.kind) - ord(tyInt) + ord(ctInt))
  of tyStatic:
    if typ.n != nil: result = mapType(lastSon typ)
    else: internalError("mapType")
  else: internalError("mapType")

proc mapReturnType(typ: PType): TCTypeKind =
  #if skipTypes(typ, typedescInst).kind == tyArray: result = ctPtr
  #else:
  result = mapType(typ)

proc isImportedType(t: PType): bool =
  result = t.sym != nil and sfImportc in t.sym.flags

proc isImportedCppType(t: PType): bool =
  result = t.sym != nil and sfInfixCall in t.sym.flags

proc getTypeDescAux(m: BModule, origTyp: PType, check: var IntSet): PNode
proc needsComplexAssignment(typ: PType): bool =
  result = containsGarbageCollectedRef(typ)

proc isObjLackingTypeField(typ: PType): bool {.inline.} =
  result = (typ.kind == tyObject) and ((tfFinal in typ.flags) and
      (typ.sons[0] == nil) or isPureObject(typ))

proc isInvalidReturnType(rettype: PType): bool =
  # Arrays and sets cannot be returned by a C procedure, because C is
  # such a poor programming language.
  # We exclude records with refs too. This enhances efficiency and
  # is necessary for proper code generation of assignments.
  if rettype == nil: result = true
  else:
    case mapType(rettype)
    of ctArray:
      result = not (skipTypes(rettype, typedescInst).kind in
          {tyVar, tyRef, tyPtr})
    of ctStruct:
      let t = skipTypes(rettype, typedescInst)
      if rettype.isImportedCppType or t.isImportedCppType: return false
      result = needsComplexAssignment(t) or
          (t.kind == tyObject and not isObjLackingTypeField(t))
    else: result = false

const
  CallingConvToStr: array[TCallingConvention, string] = ["N_NIMCALL",
    "N_STDCALL", "N_CDECL", "N_SAFECALL",
    "N_SYSCALL", # this is probably not correct for all platforms,
                 # but one can #define it to what one wants
    "N_INLINE", "N_NOINLINE", "N_FASTCALL", "N_CLOSURE", "N_NOCONV"]

proc cacheGetType(tab: TypeCache; sig: SigHash): PNode =
  # returns nil if we need to declare this type
  result = tab.getOrDefault(sig)

proc getTempName(m: BModule): PNode =
  result = atom(m.tmpBase & $m.labels)
  inc m.labels

proc ccgIntroducedPtr(s: PSym): bool =
  var pt = skipTypes(s.typ, typedescInst)
  assert skResult != s.kind
  if tfByRef in pt.flags: return true
  elif tfByCopy in pt.flags: return false
  case pt.kind
  of tyObject:
    if (optByRef in s.options) or (getSize(pt) > platform.floatSize * 2):
      result = true           # requested anyway
    elif (tfFinal in pt.flags) and (pt.sons[0] == nil):
      result = false          # no need, because no subtyping possible
    else:
      result = true           # ordinary objects are always passed by reference,
                              # otherwise casting doesn't work
  of tyTuple:
    result = (getSize(pt) > platform.floatSize*2) or (optByRef in s.options)
  else: result = false

proc fillResult(res: PSym) =
  if res.cg.isNil:
    if mapReturnType(res.typ) != ctArray and isInvalidReturnType(res.typ):
      res.cg = newTree(nkDerefExpr, atom("Result", res.typ))
    else:
      res.cg = atom"Result"
      res.cg.typ = res.typ
  when false:
    fillLoc(param.loc, locParam, param.typ, ~"Result",
            OnStack)
    if mapReturnType(param.typ) != ctArray and isInvalidReturnType(param.typ):
      incl(param.loc.flags, lfIndirect)
      param.loc.s = OnUnknown

proc fillLoc(m: BModule; s: PSym) =
  if s.cg.isNil:
    s.cg = mangleName(m, s)
    s.cg.typ = s.typ

proc typeNameOrLiteral(m: BModule; t: PType, literal: string): PNode =
  if t.sym != nil and sfImportc in t.sym.flags and t.sym.magic == mNone:
    result = t.sym.cg
  else:
    result = atom(literal)

proc getSimpleTypeDesc(m: BModule, typ: PType): PNode =
  const
    NumericalTypeToStr: array[tyInt..tyUInt64, string] = [
      "NI", "NI8", "NI16", "NI32", "NI64",
      "NF", "NF32", "NF64", "NF128",
      "NU", "NU8", "NU16", "NU32", "NU64"]
  case typ.kind
  of tyPointer:
    result = typeNameOrLiteral(m, typ, "void*")
  of tyString:
    discard cgsym(m, "NimStringDesc")
    result = typeNameOrLiteral(m, typ, "NimStringDesc*")
  of tyCString: result = typeNameOrLiteral(m, typ, "NCSTRING")
  of tyBool: result = typeNameOrLiteral(m, typ, "NIM_BOOL")
  of tyChar: result = typeNameOrLiteral(m, typ, "NIM_CHAR")
  of tyNil: result = typeNameOrLiteral(m, typ, "0")
  of tyInt..tyUInt64:
    result = typeNameOrLiteral(m, typ, NumericalTypeToStr[typ.kind])
  of tyDistinct, tyRange, tyOrdinal: result = getSimpleTypeDesc(m, typ.sons[0])
  of tyStatic:
    if typ.n != nil: result = getSimpleTypeDesc(m, lastSon typ)
    else: internalError("tyStatic for getSimpleTypeDesc")
  of tyGenericInst, tyAlias:
    result = getSimpleTypeDesc(m, lastSon typ)
  else: result = nil

proc pushType(m: BModule, typ: PType) =
  add(m.typeStack, typ)

proc getTypePre(m: BModule, typ: PType; sig: SigHash): PNode =
  if typ == nil: result = atom("void")
  else:
    result = getSimpleTypeDesc(m, typ)
    if result == nil: result = cacheGetType(m.typeCache, sig)

proc structOrUnion(t: PType): PNode =
  atom(if tfUnion in t.flags: "union" else: "struct")

proc getForwardStructFormat(m: BModule; su, name: PNode): PNode =
  if m.compileToCpp: result = newTree(nkDecl, su, name)
  else: result = newTree(nkTypeDef, su, name, name)

proc getTypeForward(m: BModule, typ: PType; sig: SigHash): PNode =
  result = cacheGetType(m.forwTypeCache, sig)
  if result != nil: return
  result = getTypePre(m, typ, sig)
  if result != nil: return
  case typ.skipTypes(abstractInst).kind
  of tySequence, tyTuple, tyObject:
    result = getTypeName(m, typ, sig)
    m.forwTypeCache[sig] = result
    if not isImportedType(typ):
      add(m.s[cfsForwardTypes], getForwardStructFormat(m, structOrUnion(typ), result))
    doAssert m.forwTypeCache[sig] == result
  else: internalError("getTypeForward(" & $typ.kind & ')')

proc getTypeDescWeak(m: BModule; t: PType; check: var IntSet): PNode =
  ## like getTypeDescAux but creates only a *weak* dependency. In other words
  ## we know we only need a pointer to it so we only generate a struct forward
  ## declaration:
  let etB = t.skipTypes(abstractInst)
  case etB.kind
  of tyObject, tyTuple:
    if isImportedCppType(etB) and t.kind == tyGenericInst:
      result = getTypeDescAux(m, t, check)
    else:
      result = getTypeForward(m, t, hashType(t))
      pushType(m, t)
  of tySequence:
    result = newTree(nkPtrTy, getTypeForward(m, t, hashType(t)))
    pushType(m, t)
  else:
    result = getTypeDescAux(m, t, check)

proc paramStorageLoc(param: PSym): TStorageLoc =
  if param.typ.skipTypes({tyVar, tyTypeDesc}).kind notin {
          tyArray, tyOpenArray, tyVarargs}:
    result = OnStack
  else:
    result = OnUnknown

proc genProcParams(m: BModule, t: PType, rettype, params: var PNode,
                   check: var IntSet, declareEnvironment=true;
                   weakDep=false) =
  params = newNode(nkPar)
  if t.sons[0] == nil or isInvalidReturnType(t.sons[0]):
    rettype = atom"void"
  else:
    rettype = getTypeDescAux(m, t.sons[0], check)
  for i in countup(1, sonsLen(t.n) - 1):
    if t.n.sons[i].kind != nkSym: internalError(t.n.info, "genProcParams")
    var param = t.n.sons[i].sym
    if isCompileTimeOnly(param.typ): continue
    fillLoc(m, param)
    var typ: PNode
    let paramName = param.cg.strVal
    if ccgIntroducedPtr(param):
      typ = newTree(nkPtrTy, getTypeDescWeak(m, param.typ, check))
      param.cg = newTree(nkDerefExpr, param.cg)
    elif weakDep:
      typ = getTypeDescWeak(m, param.typ, check)
    else:
      typ = getTypeDescAux(m, param.typ, check)
    params.add newTree(nkDecl, typ, param.cg)
    # declare the len field for open arrays:
    var arr = param.typ
    if arr.kind == tyVar: arr = arr.sons[0]
    var j = 0
    while arr.kind in {tyOpenArray, tyVarargs}:
      # this fixes the 'sort' bug:
      #if param.typ.kind == tyVar: param.loc.s = OnUnknown
      params.add newTree(nkDecl, atom"NI", atom(paramName & "Len" & $j))
      inc(j)
      arr = arr.sons[0]
  if t.sons[0] != nil and isInvalidReturnType(t.sons[0]):
    var arr = t.sons[0]
    var typ: PNode
    if mapReturnType(t.sons[0]) != ctArray:
      typ = newTree(nkPtrTy, getTypeDescWeak(m, arr, check))
    else:
      typ = getTypeDescWeak(m, arr, check)
    params.add newTree(nkDecl, typ, atom"Result")
  if t.callConv == ccClosure and declareEnvironment:
    params.add atom"void* ClEnv"
  if tfVarargs in t.flags:
    params.add atom"..."
  if params.len == 0:
    params.add atom"void"

proc mangleRecFieldName(field: PSym, rectype: PType): PNode =
  if (rectype.sym != nil) and
      ({sfImportc, sfExportc} * rectype.sym.flags != {}):
    result = field.cg
  else:
    result = atom(mangleField(field.name))
  if result == nil: internalError(field.info, "mangleRecFieldName")

proc genRecordFieldsAux(m: BModule, n: PNode,
                        accessExpr: PNode, rectype: PType,
                        check: var IntSet): PNode =
  result = newNode(nkSemiList)
  case n.kind
  of nkRecList:
    for i in countup(0, sonsLen(n) - 1):
      result.add genRecordFieldsAux(m, n.sons[i], accessExpr, rectype, check)
  of nkRecCase:
    if n.sons[0].kind != nkSym: internalError(n.info, "genRecordFieldsAux")
    result.add genRecordFieldsAux(m, n.sons[0], accessExpr, rectype, check)
    let uname = atom(mangle(n.sons[0].sym.name.s) & 'U')
    let ae = if accessExpr != nil: newDotExpr(accessExpr, uname)
             else: uname
    var unionBody = newNode(nkSemiList)
    for i in countup(1, sonsLen(n) - 1):
      case n.sons[i].kind
      of nkOfBranch, nkElse:
        let k = lastSon(n.sons[i])
        if k.kind != nkSym:
          let sname = atom("S" & $i)
          let a = genRecordFieldsAux(m, k, newDotExpr(ae, sname), rectype,
                                     check)
          if a != nil and a.len > 0:
            unionBody.add newTree(nkDecl, newTree(nkObjectTy, newNode(nkEmpty), a), sname)
        else:
          unionBody.add genRecordFieldsAux(m, k, ae, rectype, check)
      else: internalError("genRecordFieldsAux(record case branch)")
    if unionBody.len > 0:
      result.add newTree(nkDecl, newTree(nkUnion, newNode(nkEmpty), unionBody), uname)
  of nkSym:
    let field = n.sym
    if field.typ.kind == tyVoid: return
    #assert(field.ast == nil)
    let sname = mangleRecFieldName(field, rectype)
    let ae = if accessExpr != nil: newDotExpr(accessExpr, sname)
             else: sname
    fillLoc(m, field)
    # for importcpp'ed objects, we only need to set field.loc, but don't
    # have to recurse via 'getTypeDescAux'. And not doing so prevents problems
    # with heavily templatized C++ code:
    if not isImportedCppType(rectype):
      let fieldType = field.loc.t.skipTypes(abstractInst)
      if fieldType.kind == tyArray and tfUncheckedArray in fieldType.flags:
        result.add newTree(nkDecl, getTypeDescAux(m, fieldType.elemType, check), newTree(nkBracketExpr, sname, atom"SEQ_DECL_SIZE"))
      elif fieldType.kind == tySequence:
        # we need to use a weak dependency here for trecursive_table.
        result.add newTree(nkDecl, getTypeDescWeak(m, field.typ, check), sname)
      elif field.bitsize != 0:
        result.add newTree(nkDecl, getTypeDescAux(m, field.typ, check),
          newTree(nkInfix, atom":", sname, atom($field.bitsize)))
      else:
        # don't use fieldType here because we need the
        # tyGenericInst for C++ template support
        result.add newTree(nkDecl, getTypeDescAux(m, field.typ, check), sname)
  else: internalError(n.info, "genRecordFieldsAux()")

proc getRecordFields(m: BModule, typ: PType, check: var IntSet): PNode =
  result = genRecordFieldsAux(m, typ.n, nil, typ, check)

proc fillObjectFields*(m: BModule; typ: PType) =
  # sometimes generic objects are not consistently merged. We patch over
  # this fact here.
  var check = initIntSet()
  discard getRecordFields(m, typ, check)

proc getRecordDesc(m: BModule, typ: PType, name: PNode,
                   check: var IntSet): PNode =
  # declare the record:
  var hasField = false

  var decl = newNode(nkDecl)
  if tfPacked in typ.flags:
    if hasAttribute in CC[cCompiler].props:
      decl.add structOrUnion(typ)
      decl.add atom"__attribute__((__packed__))"
    else:
      decl.add atom"#pragma pack(1)\L"
      decl.add structOrUnion(typ)
  else:
    decl.add structOrUnion(typ)

  result = newNode(nkCurlyBlock)

  if typ.kind == tyObject:
    if typ.sons[0] == nil:
      if (typ.sym != nil and sfPure in typ.sym.flags) or tfFinal in typ.flags:
        discard
      else:
        discard cgsym(m, "TNimType")
        result.add newTree(nkDecl, newTree(nkPtrTy, atom"TNimType"),
          atom"m_type")
        hasField = true
    elif m.compileToCpp:
      decl.add atom": public"
      decl.add getTypeDescAux(m, typ.sons[0].skipTypes(skipPtrs), check)
      hasField = true
    else:
      result.add newTree(nkDecl, getTypeDescAux(m, typ.sons[0].skipTypes(skipPtrs), check), atom"Sup")
      hasField = true

  let desc = getRecordFields(m, typ, check)
  if desc.len == 0 and not hasField:
    result.add atom"char dummy"
  else:
    result.add desc
  decl.add result
  result = decl

proc getTupleDesc(m: BModule, typ: PType, name: PNode,
                  check: var IntSet): PNode =
  result = newTree(nkDecl, structOrUnion(typ), name)
  var desc = newNode(nkCurlyBlock)
  for i in countup(0, sonsLen(typ) - 1):
    desc.add newTree(nkDecl, getTypeDescAux(m, typ.sons[i], check),
                     atom("Field" & $i))
  if desc.len == 0: result.add atom"char dummy"
  else: result.add desc

proc scanCppGenericSlot(pat: string, cursor, outIdx, outStars: var int): bool =
  # A helper proc for handling cppimport patterns, involving numeric
  # placeholders for generic types (e.g. '0, '**2, etc).
  # pre: the cursor must be placed at the ' symbol
  # post: the cursor will be placed after the final digit
  # false will returned if the input is not recognized as a placeholder
  inc cursor
  let begin = cursor
  while pat[cursor] == '*': inc cursor
  if pat[cursor] in Digits:
    outIdx = pat[cursor].ord - '0'.ord
    outStars = cursor - begin
    inc cursor
    return true
  else:
    return false

proc resolveStarsInCppType(typ: PType, idx, stars: int): PType =
  # XXX: we should catch this earlier and report it as a semantic error
  if idx >= typ.len: internalError "invalid apostrophe type parameter index"

  result = typ.sons[idx]
  for i in 1..stars:
    if result != nil and result.len > 0:
      result = if result.kind == tyGenericInst: result.sons[1]
               else: result.elemType

const
  irrelevantForBackend = {tyGenericBody, tyGenericInst, tyGenericInvocation,
                          tyDistinct, tyRange, tyStatic, tyAlias}

proc getTypeDescAux(m: BModule, origTyp: PType, check: var IntSet): PNode =
  # returns only the type's name
  var t = origTyp.skipTypes(irrelevantForBackend)
  if t.sym != nil: useHeader(m, t.sym)
  if t != origTyp and origTyp.sym != nil: useHeader(m, origTyp.sym)
  let sig = hashType(origTyp)
  result = getTypePre(m, t, sig)
  if result != nil: return
  if containsOrIncl(check, t.id):
    if not (isImportedCppType(origTyp) or isImportedCppType(t)):
      internalError("cannot generate C type for: " & typeToString(origTyp))
    # XXX: this BUG is hard to fix -> we need to introduce helper structs,
    # but determining when this needs to be done is hard. We should split
    # C type generation into an analysis and a code generation phase somehow.
  case t.kind
  of tyRef, tyPtr, tyVar:
    var star = if t.kind == tyVar and tfVarIsPtr notin origTyp.flags and
                    compileToCpp(m): nkVarTy else: nkPtrTy
    var et = origTyp.skipTypes(abstractInst).lastSon
    var etB = et.skipTypes(abstractInst)
    if etB.kind in {tyArray, tyOpenArray, tyVarargs}:
      # this is correct! sets have no proper base type, so we treat
      # ``var set[char]`` in `getParamTypeDesc`
      et = elemType(etB)
      etB = et.skipTypes(abstractInst)
      star = nkPtrTy
    case etB.kind
    of tyObject, tyTuple:
      if isImportedCppType(etB) and et.kind == tyGenericInst:
        result = newTree(nkPtrTy, getTypeDescAux(m, et, check))
      else:
        # no restriction! We have a forward declaration for structs
        let name = getTypeForward(m, et, hashType et)
        result = newTree(star, name)
        m.typeCache[sig] = result
        pushType(m, et)
    of tySequence:
      # no restriction! We have a forward declaration for structs
      let name = getTypeForward(m, et, hashType et)
      result = newTree(star, newTree(nkPtrTy, name))
      m.typeCache[sig] = result
      pushType(m, et)
    else:
      # else we have a strong dependency  :-(
      result = newTree(star, getTypeDescAux(m, et, check))
      m.typeCache[sig] = result
  of tyOpenArray, tyVarargs:
    result = newTree(nkPtrTy, getTypeDescWeak(m, t.sons[0], check))
    m.typeCache[sig] = result
  of tyEnum:
    result = cacheGetType(m.typeCache, sig)
    if result == nil:
      result = getTypeName(m, origTyp, sig)
      if not (isImportedCppType(t) or
          (sfImportc in t.sym.flags and t.sym.magic == mNone)):
        m.typeCache[sig] = result
        var size: int
        if firstOrd(t) < 0:
          m.s[cfsTypes].add newTree(nkTypeDef, atom"NI32", result)
          size = 4
        else:
          size = int(getSize(t))
          case size
          of 1: m.s[cfsTypes].add newTree(nkTypeDef, atom"NU8", result)
          of 2: m.s[cfsTypes].add newTree(nkTypeDef, atom"NU16", result)
          of 4: m.s[cfsTypes].add newTree(nkTypeDef, atom"NI32", result)
          of 8: m.s[cfsTypes].add newTree(nkTypeDef, atom"NI64", result)
          else: internalError(t.sym.info, "getTypeDescAux: enum")
        when false:
          let owner = hashOwner(t.sym)
          if not gDebugInfo.hasEnum(t.sym.name.s, t.sym.info.line, owner):
            var vals: seq[(string, int)] = @[]
            for i in countup(0, t.n.len - 1):
              assert(t.n.sons[i].kind == nkSym)
              let field = t.n.sons[i].sym
              vals.add((field.name.s, field.position.int))
            gDebugInfo.registerEnum(EnumDesc(size: size, owner: owner, id: t.sym.id,
              name: t.sym.name.s, values: vals))
  of tyProc:
    result = getTypeName(m, origTyp, sig)
    m.typeCache[sig] = result
    var rettype, desc: PNode
    genProcParams(m, t, rettype, desc, check, true, true)
    if not isImportedType(t):
      if t.callConv != ccClosure: # procedure vars may need a closure!
        m.s[cfsTypes].add newTree(nkTypeDef,
          newTree(nkCall, atom(CallingConvToStr[t.callConv] & "_PTR"),
            rettype, result), desc)
      else:
        m.s[cfsTypes].add newTree(nkTypeDef, "typedef struct {$n" &
            "N_NIMCALL_PTR($2, ClPrc) $3;$n" &
            "void* ClEnv;$n} $1;$n",
             [result, rettype, desc])
  of tySequence:
    # we cannot use getTypeForward here because then t would be associated
    # with the name of the struct, not with the pointer to the struct:
    result = cacheGetType(m.forwTypeCache, sig)
    if result == nil:
      result = getTypeName(m, origTyp, sig)
      if not isImportedType(t):
        addf(m.s[cfsForwardTypes], getForwardStructFormat(m),
            [structOrUnion(t), result])
      m.forwTypeCache[sig] = result
    assert(cacheGetType(m.typeCache, sig) == nil)
    m.typeCache[sig] = result & "*"
    if not isImportedType(t):
      if skipTypes(t.sons[0], typedescInst).kind != tyEmpty:
        const
          cppSeq = "struct $2 : #TGenericSeq {$n"
          cSeq = "struct $2 {$n" &
                 "  #TGenericSeq Sup;$n"
        appcg(m, m.s[cfsSeqTypes],
            (if m.compileToCpp: cppSeq else: cSeq) &
            "  $1 data[SEQ_DECL_SIZE];$n" &
            "};$n", [getTypeDescAux(m, t.sons[0], check), result])
      else:
        result = atom("TGenericSeq")
    add(result, "*")
  of tyArray:
    var n: BiggestInt = lengthOrd(t)
    if n <= 0: n = 1   # make an array of at least one element
    result = getTypeName(m, origTyp, sig)
    m.typeCache[sig] = result
    if not isImportedType(t):
      let foo = getTypeDescAux(m, t.sons[1], check)
      addf(m.s[cfsTypes], "typedef $1 $2[$3];$n",
           [foo, result, atom(n)])
  of tyObject, tyTuple:
    if isImportedCppType(t) and origTyp.kind == tyGenericInst:
      # for instantiated templates we do not go through the type cache as the
      # the type cache is not aware of 'tyGenericInst'.
      let cppName = getTypeName(m, t, sig)
      var i = 0
      var chunkStart = 0
      while i < cppName.data.len:
        if cppName.data[i] == '\'':
          var chunkEnd = <i
          var idx, stars: int
          if scanCppGenericSlot(cppName.data, i, idx, stars):
            result.add cppName.data.substr(chunkStart, chunkEnd)
            chunkStart = i

            let typeInSlot = resolveStarsInCppType(origTyp, idx + 1, stars)
            if typeInSlot == nil or typeInSlot.kind == tyVoid:
              result.add(~"void")
            else:
              result.add getTypeDescAux(m, typeInSlot, check)
        else:
          inc i

      if chunkStart != 0:
        result.add cppName.data.substr(chunkStart)
      else:
        result = cppName & "<"
        for i in 1 .. origTyp.len-2:
          if i > 1: result.add(" COMMA ")
          result.add(getTypeDescAux(m, origTyp.sons[i], check))
        result.add("> ")
      # always call for sideeffects:
      assert t.kind != tyTuple
      discard getRecordDesc(m, t, result, check)
    else:
      when false:
        if t.sym != nil and t.sym.name.s == "KeyValuePair":
          if t == origTyp:
            echo "wtf: came here"
            writeStackTrace()
            quit 1
      result = cacheGetType(m.forwTypeCache, sig)
      if result == nil:
        when false:
          if t.sym != nil and t.sym.name.s == "KeyValuePair":
            # or {sfImportc, sfExportc} * t.sym.flags == {}:
            if t.cg != nil:
              echo t.kind, " ", hashType t
              echo origTyp.kind, " ", sig
            assert t.cg == nil
        result = getTypeName(m, origTyp, sig)
        m.forwTypeCache[sig] = result
        if not isImportedType(t):
          addf(m.s[cfsForwardTypes], "/* tyObject: $1 $2 $3 */", [atom typeToString t,
            atom t.id, atom m.module.id])
          addf(m.s[cfsForwardTypes], getForwardStructFormat(m),
             [structOrUnion(t), result])
        assert m.forwTypeCache[sig] == result
      m.typeCache[sig] = result # always call for sideeffects:
      let recdesc = if t.kind != tyTuple: getRecordDesc(m, t, result, check)
                    else: getTupleDesc(m, t, result, check)
      if not isImportedType(t): add(m.s[cfsTypes], recdesc)
  of tySet:
    result = getTypeName(m, t.lastSon, hashType t.lastSon) & "_Set"
    m.typeCache[sig] = result
    if not isImportedType(t):
      let s = int(getSize(t))
      case s
      of 1, 2, 4, 8: addf(m.s[cfsTypes], "typedef NU$2 $1;$n", [result, atom(s*8)])
      else: addf(m.s[cfsTypes], "typedef NU8 $1[$2];$n",
             [result, atom(getSize(t))])
  of tyGenericInst, tyDistinct, tyOrdinal, tyTypeDesc, tyAlias:
    result = getTypeDescAux(m, lastSon(t), check)
  else:
    internalError("getTypeDescAux(" & $t.kind & ')')
    result = nil
  # fixes bug #145:
  excl(check, t.id)

proc getTypeDesc(m: BModule, typ: PType): PNode =
  var check = initIntSet()
  result = getTypeDescAux(m, typ, check)

type
  TClosureTypeKind = enum
    clHalf, clHalfWithEnv, clFull

proc getClosureType(m: BModule, t: PType, kind: TClosureTypeKind): PNode =
  assert t.kind == tyProc
  var check = initIntSet()
  result = getTempName(m)
  var rettype, desc: Rope
  genProcParams(m, t, rettype, desc, check, declareEnvironment=kind != clHalf)
  if not isImportedType(t):
    if t.callConv != ccClosure or kind != clFull:
      addf(m.s[cfsTypes], "typedef $1_PTR($2, $3) $4;$n",
           [atom(CallingConvToStr[t.callConv]), rettype, result, desc])
    else:
      addf(m.s[cfsTypes], "typedef struct {$n" &
          "N_NIMCALL_PTR($2, ClPrc) $3;$n" &
          "void* ClEnv;$n} $1;$n",
           [result, rettype, desc])

proc finishTypeDescriptions(m: BModule) =
  var i = 0
  while i < len(m.typeStack):
    discard getTypeDesc(m, m.typeStack[i])
    inc(i)

template cgDeclFrmt*(s: PSym): string = s.constraint.strVal

proc genProcHeader(m: BModule, prc: PSym): PNode =
  var
    rettype, params: Rope
  genCLineDir(result, prc.info)
  # using static is needed for inline procs
  if lfExportLib in prc.loc.flags:
    if isHeaderFile in m.flags:
      result.add "N_LIB_IMPORT "
    else:
      result.add "N_LIB_EXPORT "
  elif prc.typ.callConv == ccInline:
    result.add "static "
  var check = initIntSet()
  fillLoc(m, prc)
  genProcParams(m, prc.typ, rettype, params, check)
  # careful here! don't access ``prc.ast`` as that could reload large parts of
  # the object graph!
  if prc.constraint.isNil:
    addf(result, "$1($2, $3)$4",
         [atom(CallingConvToStr[prc.typ.callConv]), rettype, prc.cg,
         params])
  else:
    result = prc.cgDeclFrmt % [rettype, prc.cg, params]

# ------------------ type info generation -------------------------------------

proc genTypeInfo(m: BModule, t: PType): PNode
proc getNimNode(m: BModule): PNode =
  result = newTree(nkBracketExpr, m.typeNodesName, atom(m.typeNodes))
  inc(m.typeNodes)

proc genTypeInfoAuxBase(m: BModule; typ, origType: PType; name, base: PNode) =
  var nimtypeKind: int
  #allocMemTI(m, typ, name)
  if isObjLackingTypeField(typ):
    nimtypeKind = ord(tyPureObject)
  else:
    nimtypeKind = ord(typ.kind)

  var size: Rope
  if tfIncompleteStruct in typ.flags: size = atom"void*"
  else: size = getTypeDesc(m, origType)
  addf(m.s[cfsTypeInit3],
       "$1.size = sizeof($2);$n" & "$1.kind = $3;$n" & "$1.base = $4;$n",
       [name, size, atom(nimtypeKind), base])
  # compute type flags for GC optimization
  var flags = 0
  if not containsGarbageCollectedRef(typ): flags = flags or 1
  if not canFormAcycle(typ): flags = flags or 2
  #else MessageOut("can contain a cycle: " & typeToString(typ))
  if flags != 0:
    addf(m.s[cfsTypeInit3], "$1.flags = $2;$n", [name, atom(flags)])
  discard cgsym(m, "TNimType")
  m.s[cfsVars].add newTree(nkDecl, atom"TNimType", name)

proc genTypeInfoAux(m: BModule, typ, origType: PType, name: PNode) =
  var base: Rope
  if sonsLen(typ) > 0 and typ.sons[0] != nil:
    var x = typ.sons[0]
    if typ.kind == tyObject: x = x.skipTypes(skipPtrs)
    base = genTypeInfo(m, x)
  else:
    base = atom("0")
  genTypeInfoAuxBase(m, typ, origType, name, base)

proc discriminatorTableName(m: BModule, objtype: PType, d: PSym): PNode =
  # bugfix: we need to search the type that contains the discriminator:
  var objtype = objtype
  while lookupInRecord(objtype.n, d.name) == nil:
    objtype = objtype.sons[0]
  if objtype.sym == nil:
    internalError(d.info, "anonymous obj with discriminator")
  result = atom("NimDT_$1_$2" % [$hashType(objtype), d.name.s.mangle])

proc discriminatorTableDecl(m: BModule, objtype: PType, d: PSym): PNode =
  discard cgsym(m, "TNimNode")
  var tmp = discriminatorTableName(m, objtype, d)
  result = newTree(nkDecl, newTree(nkPtrTy, atom"TNimNode"),
                   newTree(nkBracketExpr, tmp, atom(lengthOrd(d.typ)+1)))

proc genObjectFields(m: BModule, typ, origType: PType, n, expr: PNode) =
  case n.kind
  of nkRecList:
    var L = sonsLen(n)
    if L == 1:
      genObjectFields(m, typ, origType, n.sons[0], expr)
    elif L > 0:
      var tmp = getTempName(m)
      addf(m.s[cfsTypeInit1], "static TNimNode* $1[$2];$n", [tmp, atom(L)])
      for i in countup(0, L-1):
        var tmp2 = getNimNode(m)
        addf(m.s[cfsTypeInit3], "$1[$2] = &$3;$n", [tmp, atom(i), tmp2])
        genObjectFields(m, typ, origType, n.sons[i], tmp2)
      addf(m.s[cfsTypeInit3], "$1.len = $2; $1.kind = 2; $1.sons = &$3[0];$n",
           [expr, atom(L), tmp])
    else:
      addf(m.s[cfsTypeInit3], "$1.len = $2; $1.kind = 2;$n", [expr, atom(L)])
  of nkRecCase:
    assert(n.sons[0].kind == nkSym)
    var field = n.sons[0].sym
    var tmp = discriminatorTableName(m, typ, field)
    var L = lengthOrd(field.typ)
    assert L > 0
    addf(m.s[cfsTypeInit3], "$1.kind = 3;$n" &
        "$1.offset = offsetof($2, $3);$n" & "$1.typ = $4;$n" &
        "$1.name = $5;$n" & "$1.sons = &$6[0];$n" &
        "$1.len = $7;$n", [expr, getTypeDesc(m, origType), field.cg,
                           genTypeInfo(m, field.typ),
                           makeCString(field.name.s),
                           tmp, atom(L)])
    addf(m.s[cfsData], "TNimNode* $1[$2];$n", [tmp, atom(L+1)])
    for i in countup(1, sonsLen(n)-1):
      var b = n.sons[i]           # branch
      var tmp2 = getNimNode(m)
      genObjectFields(m, typ, origType, lastSon(b), tmp2)
      case b.kind
      of nkOfBranch:
        if sonsLen(b) < 2:
          internalError(b.info, "genObjectFields; nkOfBranch broken")
        for j in countup(0, sonsLen(b) - 2):
          if b.sons[j].kind == nkRange:
            var x = int(getOrdValue(b.sons[j].sons[0]))
            var y = int(getOrdValue(b.sons[j].sons[1]))
            while x <= y:
              addf(m.s[cfsTypeInit3], "$1[$2] = &$3;$n", [tmp, atom(x), tmp2])
              inc(x)
          else:
            addf(m.s[cfsTypeInit3], "$1[$2] = &$3;$n",
                 [tmp, atom(getOrdValue(b.sons[j])), tmp2])
      of nkElse:
        addf(m.s[cfsTypeInit3], "$1[$2] = &$3;$n",
             [tmp, atom(L), tmp2])
      else: internalError(n.info, "genObjectFields(nkRecCase)")
  of nkSym:
    var field = n.sym
    if field.bitsize == 0:
      addf(m.s[cfsTypeInit3], "$1.kind = 1;$n" &
          "$1.offset = offsetof($2, $3);$n" &
          "$1.typ = $4;$n" &
          "$1.name = $5;$n", [expr, getTypeDesc(m, origType),
          field.cg, genTypeInfo(m, field.typ), makeCString(field.name.s)])
  else: internalError(n.info, "genObjectFields")

proc genObjectInfo(m: BModule, typ, origType: PType, name: PNode) =
  if typ.kind == tyObject: genTypeInfoAux(m, typ, origType, name)
  else: genTypeInfoAuxBase(m, typ, origType, name, atom("0"))
  var tmp = getNimNode(m)
  if not isImportedCppType(typ):
    genObjectFields(m, typ, origType, typ.n, tmp)
  addf(m.s[cfsTypeInit3], "$1.node = &$2;$n", [name, tmp])
  var t = typ.sons[0]
  while t != nil:
    t = t.skipTypes(skipPtrs)
    t.flags.incl tfObjHasKids
    t = t.sons[0]

proc genTupleInfo(m: BModule, typ, origType: PType, name: PNode) =
  genTypeInfoAuxBase(m, typ, typ, name, atom("0"))
  var expr = getNimNode(m)
  var length = sonsLen(typ)
  if length > 0:
    var tmp = getTempName(m)
    addf(m.s[cfsTypeInit1], "static TNimNode* $1[$2];$n", [tmp, atom(length)])
    for i in countup(0, length - 1):
      var a = typ.sons[i]
      var tmp2 = getNimNode(m)
      addf(m.s[cfsTypeInit3], "$1[$2] = &$3;$n", [tmp, atom(i), tmp2])
      addf(m.s[cfsTypeInit3], "$1.kind = 1;$n" &
          "$1.offset = offsetof($2, Field$3);$n" &
          "$1.typ = $4;$n" &
          "$1.name = \"Field$3\";$n",
           [tmp2, getTypeDesc(m, origType), atom(i), genTypeInfo(m, a)])
    addf(m.s[cfsTypeInit3], "$1.len = $2; $1.kind = 2; $1.sons = &$3[0];$n",
         [expr, atom(length), tmp])
  else:
    addf(m.s[cfsTypeInit3], "$1.len = $2; $1.kind = 2;$n",
         [expr, atom(length)])
  addf(m.s[cfsTypeInit3], "$1.node = &$2;$n", [name, expr])

proc genEnumInfo(m: BModule, typ: PType, name: PNode) =
  # Type information for enumerations is quite heavy, so we do some
  # optimizations here: The ``typ`` field is never set, as it is redundant
  # anyway. We generate a cstring array and a loop over it. Exceptional
  # positions will be reset after the loop.
  genTypeInfoAux(m, typ, typ, name)
  var nodePtrs = getTempName(m)
  var length = sonsLen(typ.n)
  addf(m.s[cfsTypeInit1], "static TNimNode* $1[$2];$n",
       [nodePtrs, atom(length)])
  var enumNames, specialCases: Rope
  var firstNimNode = m.typeNodes
  var hasHoles = false
  for i in countup(0, length - 1):
    assert(typ.n.sons[i].kind == nkSym)
    var field = typ.n.sons[i].sym
    var elemNode = getNimNode(m)
    if field.ast == nil:
      # no explicit string literal for the enum field, so use field.name:
      add(enumNames, makeCString(field.name.s))
    else:
      add(enumNames, makeCString(field.ast.strVal))
    if i < length - 1: add(enumNames, ", " & tnl)
    if field.position != i or tfEnumHasHoles in typ.flags:
      addf(specialCases, "$1.offset = $2;$n", [elemNode, atom(field.position)])
      hasHoles = true
  var enumArray = getTempName(m)
  var counter = getTempName(m)
  addf(m.s[cfsTypeInit1], "NI $1;$n", [counter])
  addf(m.s[cfsTypeInit1], "static char* NIM_CONST $1[$2] = {$n$3};$n",
       [enumArray, atom(length), enumNames])
  addf(m.s[cfsTypeInit3], "for ($1 = 0; $1 < $2; $1++) {$n" &
      "$3[$1+$4].kind = 1;$n" & "$3[$1+$4].offset = $1;$n" &
      "$3[$1+$4].name = $5[$1];$n" & "$6[$1] = &$3[$1+$4];$n" & "}$n", [counter,
      atom(length), m.typeNodesName, atom(firstNimNode), enumArray, nodePtrs])
  add(m.s[cfsTypeInit3], specialCases)
  addf(m.s[cfsTypeInit3],
       "$1.len = $2; $1.kind = 2; $1.sons = &$3[0];$n$4.node = &$1;$n",
       [getNimNode(m), atom(length), nodePtrs, name])
  if hasHoles:
    # 1 << 2 is {ntfEnumHole}
    addf(m.s[cfsTypeInit3], "$1.flags = 1<<2;$n", [name])

proc genSetInfo(m: BModule, typ: PType, name: PNode) =
  assert(typ.sons[0] != nil)
  genTypeInfoAux(m, typ, typ, name)
  var tmp = getNimNode(m)
  addf(m.s[cfsTypeInit3], "$1.len = $2; $1.kind = 0;$n" & "$3.node = &$1;$n",
       [tmp, atom(firstOrd(typ)), name])

proc genArrayInfo(m: BModule, typ: PType, name: PNode) =
  genTypeInfoAuxBase(m, typ, typ, name, genTypeInfo(m, typ.sons[1]))

proc fakeClosureType(owner: PSym): PType =
  # we generate the same RTTI as for a tuple[pointer, ref tuple[]]
  result = newType(tyTuple, owner)
  result.rawAddSon(newType(tyPointer, owner))
  var r = newType(tyRef, owner)
  r.rawAddSon(newType(tyTuple, owner))
  result.rawAddSon(r)

type
  TTypeInfoReason = enum  ## for what do we need the type info?
    tiNew,                ## for 'new'

include ccgtrav

proc genDeepCopyProc(m: BModule; s: PSym; result: PNode) =
  genProc(m, s)
  addf(m.s[cfsTypeInit3], "$1.deepcopy =(void* (N_RAW_NIMCALL*)(void*))$2;$n",
     [result, s.cg])

proc genTypeInfo(m: BModule, t: PType): PNode =
  let origType = t
  var t = skipTypes(origType, irrelevantForBackend)

  let sig = hashType(origType)
  result = m.typeInfoMarker.getOrDefault(sig)
  if result != nil:
    return "(&".atom & result & ")".atom

  result = "NTI$1" % [atom($sig)]
  m.typeInfoMarker[sig] = result

  let owner = t.skipTypes(typedescPtrs).owner.getModule
  if owner != m.module:
    # make sure the type info is created in the owner module
    discard genTypeInfo(owner.bmod, origType)
    # reference the type info as extern here
    discard cgsym(m, "TNimType")
    discard cgsym(m, "TNimNode")
    addf(m.s[cfsVars], "extern TNimType $1; /* $2 */$n",
         [result, atom(typeToString(t))])
    return "(&".atom & result & ")".atom
  case t.kind
  of tyEmpty, tyVoid: result = atom"0"
  of tyPointer, tyBool, tyChar, tyCString, tyString, tyInt..tyUInt64, tyVar:
    genTypeInfoAuxBase(m, t, t, result, atom"0")
  of tyStatic:
    if t.n != nil: result = genTypeInfo(m, lastSon t)
    else: internalError("genTypeInfo(" & $t.kind & ')')
  of tyProc:
    if t.callConv != ccClosure:
      genTypeInfoAuxBase(m, t, t, result, atom"0")
    else:
      let x = fakeClosureType(t.owner)
      genTupleInfo(m, x, x, result)
  of tySequence, tyRef:
    genTypeInfoAux(m, t, t, result)
    if gSelectedGC >= gcMarkAndSweep:
      let markerProc = genTraverseProc(m, origType, sig, tiNew)
      addf(m.s[cfsTypeInit3], "$1.marker = $2;$n", [result, markerProc])
  of tyPtr, tyRange: genTypeInfoAux(m, t, t, result)
  of tyArray: genArrayInfo(m, t, result)
  of tySet: genSetInfo(m, t, result)
  of tyEnum: genEnumInfo(m, t, result)
  of tyObject: genObjectInfo(m, t, origType, result)
  of tyTuple:
    # if t.n != nil: genObjectInfo(m, t, result)
    # else:
    # BUGFIX: use consistently RTTI without proper field names; otherwise
    # results are not deterministic!
    genTupleInfo(m, t, origType, result)
  else: internalError("genTypeInfo(" & $t.kind & ')')
  if t.deepCopy != nil:
    genDeepCopyProc(m, t.deepCopy, result)
  elif origType.deepCopy != nil:
    genDeepCopyProc(m, origType.deepCopy, result)
  result = "(&".atom & result & ")".atom

proc genTypeSection(m: BModule, n: PNode) =
  discard
