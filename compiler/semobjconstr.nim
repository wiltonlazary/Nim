#
#
#           The Nim Compiler
#        (c) Copyright 2015 Nim Contributors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements Nim's object construction rules.

# included from sem.nim

type
  InitStatus = enum
    initUnknown
    initFull     # All  of the fields have been initialized
    initPartial  # Some of the fields have been initialized
    initNone     # None of the fields have been initialized
    initConflict # Fields from different branches have been initialized

proc mergeInitStatus(existing: var InitStatus, newStatus: InitStatus) =
  case newStatus
  of initConflict:
    existing = newStatus
  of initPartial:
    if existing in {initUnknown, initFull, initNone}:
      existing = initPartial
  of initNone:
    if existing == initUnknown:
      existing = initNone
    elif existing == initFull:
      existing = initPartial
  of initFull:
    if existing == initUnknown:
      existing = initFull
    elif existing == initNone:
      existing = initPartial
  of initUnknown:
    discard

proc locateFieldInInitExpr(field: PSym, initExpr: PNode): PNode =
  # Returns the assignment nkExprColonExpr node or nil
  let fieldId = field.name.id
  for i in 1 ..< initExpr.len:
    let assignment = initExpr[i]
    if assignment.kind != nkExprColonExpr:
      localError(initExpr.info, "incorrect object construction syntax")
      continue

    if fieldId == considerQuotedIdent(assignment[0]).id:
      return assignment

proc semConstrField(c: PContext, flags: TExprFlags,
                    field: PSym, initExpr: PNode): PNode =
  let assignment = locateFieldInInitExpr(field, initExpr)
  if assignment != nil:
    if nfSem in assignment.flags: return assignment[1]
    if not fieldVisible(c, field):
      localError(initExpr.info,
        "the field '$1' is not accessible.", [field.name.s])
      return

    var initValue = semExprFlagDispatched(c, assignment[1], flags)
    if initValue != nil:
      initValue = fitNode(c, field.typ, initValue, assignment.info)
    assignment.sons[0] = newSymNode(field)
    assignment.sons[1] = initValue
    assignment.flags.incl nfSem
    return initValue

proc caseBranchMatchesExpr(branch, matched: PNode): bool =
  for i in 0 .. (branch.len - 2):
    if exprStructuralEquivalent(branch[i], matched):
      return true

  return false

proc pickCaseBranch(caseExpr, matched: PNode): PNode =
  # XXX: Perhaps this proc already exists somewhere
  let endsWithElse = caseExpr[^1].kind == nkElse
  for i in 1 .. caseExpr.len - 1 - int(endsWithElse):
    if caseExpr[i].caseBranchMatchesExpr(matched):
      return caseExpr[i]

  if endsWithElse:
    return caseExpr[^1]

iterator directFieldsInRecList(recList: PNode): PNode =
  # XXX: We can remove this case by making all nkOfBranch nodes
  # regular. Currently, they try to avoid using nkRecList if they
  # include only a single field
  if recList.kind == nkSym:
    yield recList
  else:
    internalAssert recList.kind == nkRecList
    for field in recList:
      if field.kind != nkSym: continue
      yield field

template quoteStr(s: string): string = "'" & s & "'"

proc fieldsPresentInInitExpr(fieldsRecList, initExpr: PNode): string =
  result = ""
  for field in directFieldsInRecList(fieldsRecList):
    let assignment = locateFieldInInitExpr(field.sym, initExpr)
    if assignment != nil:
      if result.len != 0: result.add ", "
      result.add field.sym.name.s.quoteStr

proc missingMandatoryFields(fieldsRecList, initExpr: PNode): string =
  for r in directFieldsInRecList(fieldsRecList):
    if {tfNotNil, tfNeedsInit} * r.sym.typ.flags != {}:
      let assignment = locateFieldInInitExpr(r.sym, initExpr)
      if assignment == nil:
        if result == nil:
          result = r.sym.name.s
        else:
          result.add ", "
          result.add r.sym.name.s

proc checkForMissingFields(recList, initExpr: PNode) =
  let missing = missingMandatoryFields(recList, initExpr)
  if missing != nil:
    localError(initExpr.info, "fields not initialized: $1.", [missing])

proc semConstructFields(c: PContext, recNode: PNode,
                        initExpr: PNode, flags: TExprFlags): InitStatus =
  result = initUnknown

  case recNode.kind
  of nkRecList:
    for field in recNode:
      let status = semConstructFields(c, field, initExpr, flags)
      mergeInitStatus(result, status)

  of nkRecCase:
    template fieldsPresentInBranch(branchIdx: int): string =
      let branch = recNode[branchIdx]
      let fields = branch[branch.len - 1]
      fieldsPresentInInitExpr(fields, initExpr)

    template checkMissingFields(branchNode: PNode) =
      let fields = branchNode[branchNode.len - 1]
      checkForMissingFields(fields, initExpr)

    let discriminator = recNode.sons[0];
    internalAssert discriminator.kind == nkSym
    var selectedBranch = -1

    for i in 1 ..< recNode.len:
      let innerRecords = recNode[i][^1]
      let status = semConstructFields(c, innerRecords, initExpr, flags)
      if status notin {initNone, initUnknown}:
        mergeInitStatus(result, status)
        if selectedBranch != -1:
          let prevFields = fieldsPresentInBranch(selectedBranch)
          let currentFields = fieldsPresentInBranch(i)
          localError(initExpr.info,
            "The fields ($1) and ($2) cannot be initialized together, " &
            "because they are from conflicting branches in the case object.",
            [prevFields, currentFields])
          result = initConflict
        else:
          selectedBranch = i

    if selectedBranch != -1:
      let branchNode = recNode[selectedBranch]
      let flags = flags*{efAllowDestructor} + {efNeedStatic, efPreferNilResult}
      let discriminatorVal = semConstrField(c, flags,
                                            discriminator.sym, initExpr)
      if discriminatorVal == nil:
        let fields = fieldsPresentInBranch(selectedBranch)
        localError(initExpr.info,
          "you must provide a compile-time value for the discriminator '$1' " &
          "in order to prove that it's safe to initialize $2.",
          [discriminator.sym.name.s, fields])
        mergeInitStatus(result, initNone)
      else:
        let discriminatorVal = discriminatorVal.skipHidden

        template wrongBranchError(i) =
          let fields = fieldsPresentInBranch(i)
          localError(initExpr.info,
            "a case selecting discriminator '$1' with value '$2' " &
            "appears in the object construction, but the field(s) $3 " &
            "are in conflict with this value.",
            [discriminator.sym.name.s, discriminatorVal.renderTree, fields])

        if branchNode.kind != nkElse:
          if not branchNode.caseBranchMatchesExpr(discriminatorVal):
            wrongBranchError(selectedBranch)
        else:
          # With an else clause, check that all other branches don't match:
          for i in 1 .. (recNode.len - 2):
            if recNode[i].caseBranchMatchesExpr(discriminatorVal):
              wrongBranchError(i)
              break

      # When a branch is selected with a partial match, some of the fields
      # that were not initialized may be mandatory. We must check for this:
      if result == initPartial:
        checkMissingFields branchNode

    else:
      result = initNone
      let discriminatorVal = semConstrField(c, flags + {efPreferStatic},
                                            discriminator.sym, initExpr)
      if discriminatorVal == nil:
        # None of the branches were explicitly selected by the user and no
        # value was given to the discrimator. We can assume that it will be
        # initialized to zero and this will select a particular branch as
        # a result:
        let matchedBranch = recNode.pickCaseBranch newIntLit(0)
        checkMissingFields matchedBranch
      else:
        result = initPartial
        if discriminatorVal.kind == nkIntLit:
          # When the discriminator is a compile-time value, we also know
          # which brach will be selected:
          let matchedBranch = recNode.pickCaseBranch discriminatorVal
          if matchedBranch != nil: checkMissingFields matchedBranch
        else:
          # All bets are off. If any of the branches has a mandatory
          # fields we must produce an error:
          for i in 1 ..< recNode.len: checkMissingFields recNode[i]

  of nkSym:
    let field = recNode.sym
    let e = semConstrField(c, flags, field, initExpr)
    result = if e != nil: initFull else: initNone

  else:
    internalAssert false

proc semConstructType(c: PContext, initExpr: PNode,
                      t: PType, flags: TExprFlags): InitStatus =
  var t = t
  result = initUnknown

  while true:
    let status = semConstructFields(c, t.n, initExpr, flags)
    mergeInitStatus(result, status)

    if status in {initPartial, initNone, initUnknown}:
      checkForMissingFields t.n, initExpr

    let base = t.sons[0]
    if base == nil: break
    t = skipTypes(base, skipPtrs)

proc semObjConstr(c: PContext, n: PNode, flags: TExprFlags): PNode =
  var t = semTypeNode(c, n.sons[0], nil)
  result = newNodeIT(nkObjConstr, n.info, t)
  for child in n: result.add child

  t = skipTypes(t, {tyGenericInst, tyAlias})
  if t.kind == tyRef: t = skipTypes(t.sons[0], {tyGenericInst, tyAlias})
  if t.kind != tyObject:
    localError(n.info, errGenerated, "object constructor needs an object type")
    return

  # Check if the object is fully initialized by recursively testing each
  # field (if this is a case object, initialized fields in two different
  # branches will be reported as an error):
  let initResult = semConstructType(c, result, t, flags)

  # It's possible that the object was not fully initialized while
  # specifying a .requiresInit. pragma.
  # XXX: Turn this into an error in the next release
  if tfNeedsInit in t.flags and initResult != initFull:
    # XXX: Disable this warning for now, because tfNeedsInit is propagated
    # too aggressively from fields to object types (and this is not correct
    # in case objects)
    when false: message(n.info, warnUser,
      "object type uses the 'requiresInit' pragma, but not all fields " &
      "have been initialized. future versions of Nim will treat this as " &
      "an error")

  # Since we were traversing the object fields, it's possible that
  # not all of the fields specified in the constructor was visited.
  # We'll check for such fields here:
  for i in 1..<result.len:
    let field = result[i]
    if nfSem notin field.flags:
      if field.kind != nkExprColonExpr:
        localError(n.info, "incorrect object construction syntax")
        continue
      let id = considerQuotedIdent(field[0])
      # This node was not processed. There are two possible reasons:
      # 1) It was shadowed by a field with the same name on the left
      for j in 1 ..< i:
        let prevId = considerQuotedIdent(result[j][0])
        if prevId.id == id.id:
          localError(field.info, errFieldInitTwice, id.s)
          return
      # 2) No such field exists in the constructed type
      localError(field.info, errUndeclaredFieldX, id.s)
      return

