discard """
  cmd:      "nim c -r --styleCheck:hint --panics:on $options $file"
  targets:  "c"
  nimout:   ""
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""
include uri


block:
  let org = "udp://[2001:0db8:85a3:0000:0000:8a2e:0370:7334]:8080"
  let url = parseUri(org)
  doAssert url.hostname == "2001:0db8:85a3:0000:0000:8a2e:0370:7334" # true
  let newUrl = parseUri($url)
  doAssert newUrl.hostname == "2001:0db8:85a3:0000:0000:8a2e:0370:7334" # true


block:
  block:
    const test1 = "abc\L+def xyz"
    doAssert encodeUrl(test1) == "abc%0A%2Bdef+xyz"
    doAssert decodeUrl(encodeUrl(test1)) == test1
    doAssert encodeUrl(test1, false) == "abc%0A%2Bdef%20xyz"
    doAssert decodeUrl(encodeUrl(test1, false), false) == test1
    doAssert decodeUrl(encodeUrl(test1)) == test1

  block:
    let str = "http://localhost"
    let test = parseUri(str)
    doAssert test.path == ""

  block:
    let str = "http://localhost/"
    let test = parseUri(str)
    doAssert test.path == "/"

  block:
    let str = "http://localhost:8080/test"
    let test = parseUri(str)
    doAssert test.scheme == "http"
    doAssert test.port == "8080"
    doAssert test.path == "/test"
    doAssert test.hostname == "localhost"
    doAssert($test == str)

  block:
    let str = "foo://username:password@example.com:8042/over/there" &
              "/index.dtb?type=animal&name=narwhal#nose"
    let test = parseUri(str)
    doAssert test.scheme == "foo"
    doAssert test.username == "username"
    doAssert test.password == "password"
    doAssert test.hostname == "example.com"
    doAssert test.port == "8042"
    doAssert test.path == "/over/there/index.dtb"
    doAssert test.query == "type=animal&name=narwhal"
    doAssert test.anchor == "nose"
    doAssert($test == str)

  block:
    # IPv6 address
    let str = "foo://[::1]:1234/bar?baz=true&qux#quux"
    let uri = parseUri(str)
    doAssert uri.scheme == "foo"
    doAssert uri.hostname == "::1"
    doAssert uri.port == "1234"
    doAssert uri.path == "/bar"
    doAssert uri.query == "baz=true&qux"
    doAssert uri.anchor == "quux"

  block:
    let str = "urn:example:animal:ferret:nose"
    let test = parseUri(str)
    doAssert test.scheme == "urn"
    doAssert test.path == "example:animal:ferret:nose"
    doAssert($test == str)

  block:
    let str = "mailto:username@example.com?subject=Topic"
    let test = parseUri(str)
    doAssert test.scheme == "mailto"
    doAssert test.username == "username"
    doAssert test.hostname == "example.com"
    doAssert test.query == "subject=Topic"
    doAssert($test == str)

  block:
    let str = "magnet:?xt=urn:sha1:72hsga62ba515sbd62&dn=foobar"
    let test = parseUri(str)
    doAssert test.scheme == "magnet"
    doAssert test.query == "xt=urn:sha1:72hsga62ba515sbd62&dn=foobar"
    doAssert($test == str)

  block:
    let str = "/test/foo/bar?q=2#asdf"
    let test = parseUri(str)
    doAssert test.scheme == ""
    doAssert test.path == "/test/foo/bar"
    doAssert test.query == "q=2"
    doAssert test.anchor == "asdf"
    doAssert($test == str)

  block:
    let str = "test/no/slash"
    let test = parseUri(str)
    doAssert test.path == "test/no/slash"
    doAssert($test == str)

  block:
    let str = "//git@github.com:dom96/packages"
    let test = parseUri(str)
    doAssert test.scheme == ""
    doAssert test.username == "git"
    doAssert test.hostname == "github.com"
    doAssert test.port == "dom96"
    doAssert test.path == "/packages"

  block:
    let str = "file:///foo/bar/baz.txt"
    let test = parseUri(str)
    doAssert test.scheme == "file"
    doAssert test.username == ""
    doAssert test.hostname == ""
    doAssert test.port == ""
    doAssert test.path == "/foo/bar/baz.txt"

  # Remove dot segments tests
  block:
    doAssert removeDotSegments("/foo/bar/baz") == "/foo/bar/baz"

  # Combine tests
  block:
    let concat = combine(parseUri("http://google.com/foo/bar/"), parseUri("baz"))
    doAssert concat.path == "/foo/bar/baz"
    doAssert concat.hostname == "google.com"
    doAssert concat.scheme == "http"

  block:
    let concat = combine(parseUri("http://google.com/foo"), parseUri("/baz"))
    doAssert concat.path == "/baz"
    doAssert concat.hostname == "google.com"
    doAssert concat.scheme == "http"

  block:
    let concat = combine(parseUri("http://google.com/foo/test"), parseUri("bar"))
    doAssert concat.path == "/foo/bar"

  block:
    let concat = combine(parseUri("http://google.com/foo/test"), parseUri("/bar"))
    doAssert concat.path == "/bar"

  block:
    let concat = combine(parseUri("http://google.com/foo/test"), parseUri("bar"))
    doAssert concat.path == "/foo/bar"

  block:
    let concat = combine(parseUri("http://google.com/foo/test/"), parseUri("bar"))
    doAssert concat.path == "/foo/test/bar"

  block:
    let concat = combine(parseUri("http://google.com/foo/test/"), parseUri("bar/"))
    doAssert concat.path == "/foo/test/bar/"

  block:
    let concat = combine(parseUri("http://google.com/foo/test/"), parseUri("bar/"),
                         parseUri("baz"))
    doAssert concat.path == "/foo/test/bar/baz"

  # `/` tests
  block:
    let test = parseUri("http://example.com/foo") / "bar/asd"
    doAssert test.path == "/foo/bar/asd"

  block:
    let test = parseUri("http://example.com/foo/") / "/bar/asd"
    doAssert test.path == "/foo/bar/asd"

  # removeDotSegments tests
  block:
    # empty test
    doAssert removeDotSegments("") == ""

  # bug #3207
  block:
    doAssert parseUri("http://qq/1").combine(parseUri("https://qqq")).`$` == "https://qqq"

  # bug #4959
  block:
    let foo = parseUri("http://example.com") / "/baz"
    doAssert foo.path == "/baz"

  # bug found on stream 13/10/17
  block:
    let foo = parseUri("http://localhost:9515") / "status"
    doAssert $foo == "http://localhost:9515/status"

  # bug #6649 #6652
  block:
    var foo = parseUri("http://example.com")
    foo.hostname = "example.com"
    foo.path = "baz"
    doAssert $foo == "http://example.com/baz"

    foo.hostname = "example.com/"
    foo.path = "baz"
    doAssert $foo == "http://example.com/baz"

    foo.hostname = "example.com"
    foo.path = "/baz"
    doAssert $foo == "http://example.com/baz"

    foo.hostname = "example.com/"
    foo.path = "/baz"
    doAssert $foo == "http://example.com/baz"

    foo.hostname = "example.com/"
    foo.port = "8000"
    foo.path = "baz"
    doAssert $foo == "http://example.com:8000/baz"

    foo = parseUri("file:/dir/file")
    foo.path = "relative"
    doAssert $foo == "file:relative"

  # isAbsolute tests
  block:
    doAssert "www.google.com".parseUri().isAbsolute() == false
    doAssert "http://www.google.com".parseUri().isAbsolute() == true
    doAssert "file:/dir/file".parseUri().isAbsolute() == true
    doAssert "file://localhost/dir/file".parseUri().isAbsolute() == true
    doAssert "urn:ISSN:1535-3613".parseUri().isAbsolute() == true

    # path-relative URL *relative
    doAssert "about".parseUri().isAbsolute == false
    doAssert "about/staff.html".parseUri().isAbsolute == false
    doAssert "about/staff.html?".parseUri().isAbsolute == false
    doAssert "about/staff.html?parameters".parseUri().isAbsolute == false

    # absolute-path-relative URL *relative
    doAssert "/".parseUri().isAbsolute == false
    doAssert "/about".parseUri().isAbsolute == false
    doAssert "/about/staff.html".parseUri().isAbsolute == false
    doAssert "/about/staff.html?".parseUri().isAbsolute == false
    doAssert "/about/staff.html?parameters".parseUri().isAbsolute == false

    # scheme-relative URL *relative
    doAssert "//username:password@example.com:8888".parseUri().isAbsolute == false
    doAssert "//username@example.com".parseUri().isAbsolute == false
    doAssert "//example.com".parseUri().isAbsolute == false
    doAssert "//example.com/".parseUri().isAbsolute == false
    doAssert "//example.com/about".parseUri().isAbsolute == false
    doAssert "//example.com/about/staff.html".parseUri().isAbsolute == false
    doAssert "//example.com/about/staff.html?".parseUri().isAbsolute == false
    doAssert "//example.com/about/staff.html?parameters".parseUri().isAbsolute == false

    # absolute URL *absolute
    doAssert "https://username:password@example.com:8888".parseUri().isAbsolute == true
    doAssert "https://username@example.com".parseUri().isAbsolute == true
    doAssert "https://example.com".parseUri().isAbsolute == true
    doAssert "https://example.com/".parseUri().isAbsolute == true
    doAssert "https://example.com/about".parseUri().isAbsolute == true
    doAssert "https://example.com/about/staff.html".parseUri().isAbsolute == true
    doAssert "https://example.com/about/staff.html?".parseUri().isAbsolute == true
    doAssert "https://example.com/about/staff.html?parameters".parseUri().isAbsolute == true

  # encodeQuery tests
  block:
    doAssert encodeQuery({:}) == ""
    doAssert encodeQuery({"foo": "bar"}) == "foo=bar"
    doAssert encodeQuery({"foo": "bar & baz"}) == "foo=bar+%26+baz"
    doAssert encodeQuery({"foo": "bar & baz"}, usePlus = false) == "foo=bar%20%26%20baz"
    doAssert encodeQuery({"foo": ""}) == "foo"
    doAssert encodeQuery({"foo": ""}, omitEq = false) == "foo="
    doAssert encodeQuery({"a": "1", "b": "", "c": "3"}) == "a=1&b&c=3"
    doAssert encodeQuery({"a": "1", "b": "", "c": "3"}, omitEq = false) == "a=1&b=&c=3"

    block:
      var foo = parseUri("http://example.com") / "foo" ? {"bar": "1", "baz": "qux"}
      var foo1 = parseUri("http://example.com/foo?bar=1&baz=qux")
      doAssert foo == foo1

    block:
      var foo = parseUri("http://example.com") / "foo" ? {"do": "do", "bar": ""}
      var foo1 = parseUri("http://example.com/foo?do=do&bar")
      doAssert foo == foo1

  block dataUriBase64:
    doAssert getDataUri("", "text/plain") == "data:text/plain;charset=utf-8;base64,"
    doAssert getDataUri(" ", "text/plain") == "data:text/plain;charset=utf-8;base64,IA=="
    doAssert getDataUri("c\xf7>", "text/plain") == "data:text/plain;charset=utf-8;base64,Y/c+"
    doAssert getDataUri("Hello World", "text/plain") == "data:text/plain;charset=utf-8;base64,SGVsbG8gV29ybGQ="
    doAssert getDataUri("leasure.", "text/plain") == "data:text/plain;charset=utf-8;base64,bGVhc3VyZS4="
    doAssert getDataUri("""!@#$%^&*()_+""", "text/plain") == "data:text/plain;charset=utf-8;base64,IUAjJCVeJiooKV8r"
    doAssert(getDataUri("the quick brown dog jumps over the lazy fox", "text/plain") ==
      "data:text/plain;charset=utf-8;base64,dGhlIHF1aWNrIGJyb3duIGRvZyBqdW1wcyBvdmVyIHRoZSBsYXp5IGZveA==")
    doAssert(getDataUri("""The present is theirs
      The future, for which I really worked, is mine.""", "text/plain") ==
      "data:text/plain;charset=utf-8;base64,VGhlIHByZXNlbnQgaXMgdGhlaXJzCiAgICAgIFRoZSBmdXR1cmUsIGZvciB3aGljaCBJIHJlYWxseSB3b3JrZWQsIGlzIG1pbmUu")
