import system

type Bar[T] = ref object
 value: T

type types = int32|int64 # if I change this to just int32 or int64 it works (compiles)

# if I replace Bar everywhere with seq it also compiles fine
proc Foo[T: Bar[types]](): T =
 when T is Bar: nil

discard Foo[Bar[int32]]()
#bug #6073
