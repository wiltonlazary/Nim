import os, tables, strutils, times, heapqueue, options, deques

# TODO: This shouldn't need to be included, but should ideally be exported.
type
  CallbackFunc = proc () {.closure, gcsafe.}

  CallbackList = object
    function: CallbackFunc
    next: ref CallbackList

  FutureBase* = ref object of RootObj ## Untyped future.
    callbacks: CallbackList

    finished: bool
    error*: ref Exception ## Stored exception
    errorStackTrace*: string
    when not defined(release):
      stackTrace: string ## For debugging purposes only.
      id: int
      fromProc: string

  Future*[T] = ref object of FutureBase ## Typed future.
    value: T ## Stored value

  FutureVar*[T] = distinct Future[T]

  FutureError* = object of Exception
    cause*: FutureBase

{.deprecated: [PFutureBase: FutureBase, PFuture: Future].}

when not defined(release):
  var currentID = 0

var callSoonProc {.threadvar.}: proc (cbproc: proc ()) {.gcsafe.}

proc getCallSoonProc*(): (proc(cbproc: proc ()) {.gcsafe.}) =
  ## Get current implementation of ``callSoon``.
  return callSoonProc

proc setCallSoonProc*(p: (proc(cbproc: proc ()) {.gcsafe.})) =
  ## Change current implementation of ``callSoon``. This is normally called when dispatcher from ``asyncdispatcher`` is initialized.
  callSoonProc = p

proc callSoon*(cbproc: proc ()) =
  ## Call ``cbproc`` "soon".
  ##
  ## If async dispatcher is running, ``cbproc`` will be executed during next dispatcher tick.
  ##
  ## If async dispatcher is not running, ``cbproc`` will be executed immediately.
  if callSoonProc.isNil:
    # Loop not initialized yet. Call the function directly to allow setup code to use futures.
    cbproc()
  else:
    callSoonProc(cbproc)

template setupFutureBase(fromProc: string) =
  new(result)
  result.finished = false
  when not defined(release):
    result.stackTrace = getStackTrace()
    result.id = currentID
    result.fromProc = fromProc
    currentID.inc()

proc newFuture*[T](fromProc: string = "unspecified"): Future[T] =
  ## Creates a new future.
  ##
  ## Specifying ``fromProc``, which is a string specifying the name of the proc
  ## that this future belongs to, is a good habit as it helps with debugging.
  setupFutureBase(fromProc)

proc newFutureVar*[T](fromProc = "unspecified"): FutureVar[T] =
  ## Create a new ``FutureVar``. This Future type is ideally suited for
  ## situations where you want to avoid unnecessary allocations of Futures.
  ##
  ## Specifying ``fromProc``, which is a string specifying the name of the proc
  ## that this future belongs to, is a good habit as it helps with debugging.
  result = FutureVar[T](newFuture[T](fromProc))

proc clean*[T](future: FutureVar[T]) =
  ## Resets the ``finished`` status of ``future``.
  Future[T](future).finished = false
  Future[T](future).error = nil

proc checkFinished[T](future: Future[T]) =
  ## Checks whether `future` is finished. If it is then raises a
  ## ``FutureError``.
  when not defined(release):
    if future.finished:
      var msg = ""
      msg.add("An attempt was made to complete a Future more than once. ")
      msg.add("Details:")
      msg.add("\n  Future ID: " & $future.id)
      msg.add("\n  Created in proc: " & future.fromProc)
      msg.add("\n  Stack trace to moment of creation:")
      msg.add("\n" & indent(future.stackTrace.strip(), 4))
      when T is string:
        msg.add("\n  Contents (string): ")
        msg.add("\n" & indent(future.value.repr, 4))
      msg.add("\n  Stack trace to moment of secondary completion:")
      msg.add("\n" & indent(getStackTrace().strip(), 4))
      var err = newException(FutureError, msg)
      err.cause = future
      raise err

proc call(callbacks: var CallbackList) =
  var current = callbacks

  while true:
    if not current.function.isNil:
      callSoon(current.function)

    if current.next.isNil:
      break
    else:
      current = current.next[]

  # callback will be called only once, let GC collect them now
  callbacks.next = nil
  callbacks.function = nil

proc add(callbacks: var CallbackList, function: CallbackFunc) =
  if callbacks.function.isNil:
    callbacks.function = function
    assert callbacks.next == nil
  else:
    let newNext = new(ref CallbackList)
    newNext.function = callbacks.function
    newNext.next = callbacks.next
    callbacks.next = newNext
    callbacks.function = function

proc complete*[T](future: Future[T], val: T) =
  ## Completes ``future`` with value ``val``.
  #assert(not future.finished, "Future already finished, cannot finish twice.")
  checkFinished(future)
  assert(future.error == nil)
  future.value = val
  future.finished = true
  future.callbacks.call()

proc complete*(future: Future[void]) =
  ## Completes a void ``future``.
  #assert(not future.finished, "Future already finished, cannot finish twice.")
  checkFinished(future)
  assert(future.error == nil)
  future.finished = true
  future.callbacks.call()

proc complete*[T](future: FutureVar[T]) =
  ## Completes a ``FutureVar``.
  template fut: untyped = Future[T](future)
  checkFinished(fut)
  assert(fut.error == nil)
  fut.finished = true
  fut.callbacks.call()

proc complete*[T](future: FutureVar[T], val: T) =
  ## Completes a ``FutureVar`` with value ``val``.
  ##
  ## Any previously stored value will be overwritten.
  template fut: untyped = Future[T](future)
  checkFinished(fut)
  assert(fut.error.isNil())
  fut.finished = true
  fut.value = val
  fut.callbacks.call()

proc fail*[T](future: Future[T], error: ref Exception) =
  ## Completes ``future`` with ``error``.
  #assert(not future.finished, "Future already finished, cannot finish twice.")
  checkFinished(future)
  future.finished = true
  future.error = error
  future.errorStackTrace =
    if getStackTrace(error) == "": getStackTrace() else: getStackTrace(error)
  future.callbacks.call()

proc clearCallbacks(future: FutureBase) =
  future.callbacks.function = nil
  future.callbacks.next = nil

proc addCallback*(future: FutureBase, cb: proc() {.closure,gcsafe.}) =
  ## Adds the callbacks proc to be called when the future completes.
  ##
  ## If future has already completed then ``cb`` will be called immediately.
  assert cb != nil
  if future.finished:
    callSoon(cb)
  else:
    future.callbacks.add cb

proc addCallback*[T](future: Future[T],
                     cb: proc (future: Future[T]) {.closure,gcsafe.}) =
  ## Adds the callbacks proc to be called when the future completes.
  ##
  ## If future has already completed then ``cb`` will be called immediately.
  future.addCallback(
    proc() =
      cb(future)
  )

proc `callback=`*(future: FutureBase, cb: proc () {.closure,gcsafe.}) =
  ## Clears the list of callbacks and sets the callback proc to be called when the future completes.
  ##
  ## If future has already completed then ``cb`` will be called immediately.
  ##
  ## It's recommended to use ``addCallback`` or ``then`` instead.
  future.clearCallbacks
  future.addCallback cb

proc `callback=`*[T](future: Future[T],
    cb: proc (future: Future[T]) {.closure,gcsafe.}) =
  ## Sets the callback proc to be called when the future completes.
  ##
  ## If future has already completed then ``cb`` will be called immediately.
  future.callback = proc () = cb(future)

proc injectStacktrace[T](future: Future[T]) =
  # TODO: Come up with something better.
  when not defined(release):
    var msg = ""
    msg.add("\n  " & future.fromProc & "'s lead up to read of failed Future:")

    if not future.errorStackTrace.isNil and future.errorStackTrace != "":
      msg.add("\n" & indent(future.errorStackTrace.strip(), 4))
    else:
      msg.add("\n    Empty or nil stack trace.")
    future.error.msg.add(msg)

proc read*[T](future: Future[T] | FutureVar[T]): T =
  ## Retrieves the value of ``future``. Future must be finished otherwise
  ## this function will fail with a ``ValueError`` exception.
  ##
  ## If the result of the future is an error then that error will be raised.
  {.push hint[ConvFromXtoItselfNotNeeded]: off.}
  let fut = Future[T](future)
  {.pop.}
  if fut.finished:
    if fut.error != nil:
      injectStacktrace(fut)
      raise fut.error
    when T isnot void:
      return fut.value
  else:
    # TODO: Make a custom exception type for this?
    raise newException(ValueError, "Future still in progress.")

proc readError*[T](future: Future[T]): ref Exception =
  ## Retrieves the exception stored in ``future``.
  ##
  ## An ``ValueError`` exception will be thrown if no exception exists
  ## in the specified Future.
  if future.error != nil: return future.error
  else:
    raise newException(ValueError, "No error in future.")

proc mget*[T](future: FutureVar[T]): var T =
  ## Returns a mutable value stored in ``future``.
  ##
  ## Unlike ``read``, this function will not raise an exception if the
  ## Future has not been finished.
  result = Future[T](future).value

proc finished*[T](future: Future[T] | FutureVar[T]): bool =
  ## Determines whether ``future`` has completed.
  ##
  ## ``True`` may indicate an error or a value. Use ``failed`` to distinguish.
  when future is FutureVar[T]:
    result = (Future[T](future)).finished
  else:
    result = future.finished

proc failed*(future: FutureBase): bool =
  ## Determines whether ``future`` completed with an error.
  return future.error != nil

proc asyncCheck*[T](future: Future[T]) =
  ## Sets a callback on ``future`` which raises an exception if the future
  ## finished with an error.
  ##
  ## This should be used instead of ``discard`` to discard void futures.
  future.callback =
    proc () =
      if future.failed:
        injectStacktrace(future)
        raise future.error

proc `and`*[T, Y](fut1: Future[T], fut2: Future[Y]): Future[void] =
  ## Returns a future which will complete once both ``fut1`` and ``fut2``
  ## complete.
  var retFuture = newFuture[void]("asyncdispatch.`and`")
  fut1.callback =
    proc () =
      if not retFuture.finished:
        if fut1.failed: retFuture.fail(fut1.error)
        elif fut2.finished: retFuture.complete()
  fut2.callback =
    proc () =
      if not retFuture.finished:
        if fut2.failed: retFuture.fail(fut2.error)
        elif fut1.finished: retFuture.complete()
  return retFuture

proc `or`*[T, Y](fut1: Future[T], fut2: Future[Y]): Future[void] =
  ## Returns a future which will complete once either ``fut1`` or ``fut2``
  ## complete.
  var retFuture = newFuture[void]("asyncdispatch.`or`")
  proc cb[X](fut: Future[X]) =
    if fut.failed: retFuture.fail(fut.error)
    if not retFuture.finished: retFuture.complete()
  fut1.callback = cb[T]
  fut2.callback = cb[Y]
  return retFuture

proc all*[T](futs: varargs[Future[T]]): auto =
  ## Returns a future which will complete once
  ## all futures in ``futs`` complete.
  ## If the argument is empty, the returned future completes immediately.
  ##
  ## If the awaited futures are not ``Future[void]``, the returned future
  ## will hold the values of all awaited futures in a sequence.
  ##
  ## If the awaited futures *are* ``Future[void]``,
  ## this proc returns ``Future[void]``.

  when T is void:
    var
      retFuture = newFuture[void]("asyncdispatch.all")
      completedFutures = 0

    let totalFutures = len(futs)

    for fut in futs:
      fut.addCallback proc (f: Future[T]) =
        inc(completedFutures)
        if not retFuture.finished:
          if f.failed:
            retFuture.fail(f.error)
          else:
            if completedFutures == totalFutures:
              retFuture.complete()

    if totalFutures == 0:
      retFuture.complete()

    return retFuture

  else:
    var
      retFuture = newFuture[seq[T]]("asyncdispatch.all")
      retValues = newSeq[T](len(futs))
      completedFutures = 0

    for i, fut in futs:
      proc setCallback(i: int) =
        fut.addCallback proc (f: Future[T]) =
          inc(completedFutures)
          if not retFuture.finished:
            if f.failed:
              retFuture.fail(f.error)
            else:
              retValues[i] = f.read()

              if completedFutures == len(retValues):
                retFuture.complete(retValues)

      setCallback(i)

    if retValues.len == 0:
      retFuture.complete(retValues)

    return retFuture
