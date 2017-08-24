discard """
  output: '''ok'''
  cmd: "nim c -r --gc:refc -d:useGcAssert -d:useSysAssert -d:fulldebug -d:smokeCycles $file"
"""
# bug #6234
type
    Foo = ref object
        s: seq[Bar]
    Bar = ref object
        f: Foo

proc test() =
    var f = Foo.new()
    for i in 0 .. 5:
        f.s = @[]
        for j in 0 .. 5:
            var b = Bar.new()
            b.f = f
            f.s.add(b)

test()
echo "ok"
