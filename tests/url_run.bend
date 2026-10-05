import Base
import ../src/message.bend as M
import ../src/url.bend as U

# Runtime tests for url.bend, on both lanes:
#   bend tests/url_run.bend
#   bend tests/url_run.bend -o /tmp/url_run && /tmp/url_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL". These cover
# what is too large for checker evaluation: ports near and past 65535,
# hostile digit strings (must fail, never abort), long inputs, sweeps.

# Helpers
# -------

def scheme_is(a: M.Scheme, b: M.Scheme) -> Bool:
  match a b:
    case M.Http{} M.Http{}:
      True{}
    case M.Https{} M.Https{}:
      True{}
    case _ _:
      False{}

# String equality as a loop (Base's String.eq nests a call per char, which
# overflows the JS lane's stack near 15000 chars).
def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def str_eq(a: String, b: String) -> Bool:
  str_eq.go(a, b, True{})

def url_eq(a: M.Url, b: M.Url) -> Bool:
  match a b:
    case M.Url{s1, h1, p1, t1} M.Url{s2, h2, p2, t2}:
      scheme_is(s1, s2) && str_eq(h1, h2) && Nat.is_eq(p1, p2) && str_eq(t1, t2)

def done_is(r: Result<&2, &2, M.Error, M.Url>, u: M.Url) -> Bool:
  match r:
    case Done{v}:
      url_eq(v, u)
    case Fail{e}:
      False{}

def http(h: String, p: Nat, t: String) -> M.Url:
  M.Url{M.Http{}, h, p, t}

def https(h: String, p: Nat, t: String) -> M.Url:
  M.Url{M.Https{}, h, p, t}

def parses(s: String, u: M.Url) -> Bool:
  done_is(U.parse(s), u)

def fail_is(r: Result<&2, &2, M.Error, M.Url>, reason: String) -> Bool:
  match r:
    case Fail{e}:
      match e:
        case M.BadUrl{x}:
          String.eq(x, reason)
        case _:
          False{}
    case Done{v}:
      False{}

def fails_with(s: String, reason: String) -> Bool:
  fail_is(U.parse(s), reason)

def fails(s: String) -> Bool:
  Result.is_fail(&2, &2, M.Error, M.Url, U.parse(s))

# ok(u) and parse(show(u)) == Done{u}
def rt(+u: M.Url) -> Bool:
  U.ok(u) && done_is(U.parse(U.show(u)), u)

# n copies of a char, prepended to acc (a loop)
def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rep(n: Nat, c: Char) -> String:
  rep.go(n, c, SNil{})

# Roundtrip for ports p, p - step, p - 2 step, ... (both schemes), while p > 0.
# Structural on a fuel count k.
def port_sweep(k: Nat, +p: Nat, +step: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+q:
      rt(http("h", p, "/")) && rt(https("example.com", p, "/a?b"))
        && port_sweep(q, Nat.sub(p, step), step)

# parse("http://h:" ++ show(p)) for p > 65535 must fail.
def high_port(+p: Nat) -> Bool:
  fails_with("http://h:" ++ Nat.show(p) ++ "/", "port out of range")

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    # default and explicit ports
    ("default http", parses("http://example.com", http("example.com", 80n, "/"))),
    ("default https", parses("https://example.com/", https("example.com", 443n, "/"))),
    ("explicit 8080", parses("http://example.com:8080/a?b=c", http("example.com", 8080n, "/a?b=c"))),
    ("explicit default", parses("https://h:443/x", https("h", 443n, "/x"))),
    ("https on 80", parses("https://h:80/", https("h", 80n, "/"))),
    ("port 1", parses("http://h:1", http("h", 1n, "/"))),
    ("port 65535", parses("http://h:65535/", http("h", 65535n, "/"))),
    ("port leading zeros", parses("http://h:000000000000000000000080/", http("h", 80n, "/"))),
    # bad ports: must fail, never abort
    ("port 0", fails_with("http://h:0/", "port out of range")),
    ("port 65536", fails_with("http://h:65536/", "port out of range")),
    ("port 99999", fails_with("http://h:99999/", "port out of range")),
    ("port LIMIT", fails_with("http://h:4294967295/", "port out of range")),
    ("port LIMIT+1", fails_with("http://h:4294967296/", "port out of range")),
    ("port 2^48", fails_with("http://h:281474976710656/", "port out of range")),
    ("port 26 nines", fails_with("http://h:99999999999999999999999999/", "port out of range")),
    ("port 5000 nines", fails_with("http://h:" ++ rep(5000n, '9') ++ "/", "port out of range")),
    ("port 5000 nines then x", fails_with("http://h:" ++ rep(5000n, '9') ++ "x/", "bad port")),
    ("high ports", high_port(65536n) && high_port(70000n) && high_port(100000n) && high_port(16777216n)),
    ("empty port", fails_with("http://h:/", "empty port") && fails_with("http://h:", "empty port")),
    ("port junk", fails_with("http://h:8o/", "bad port") && fails_with("http://h:-80/", "bad port")
      && fails_with("http://h:80:80/", "bad port") && fails_with("http://h:0x50/", "bad port")),
    # uppercase scheme / host
    ("uppercase", parses("HTTPS://WWW.EXAMPLE.COM:8443/A/B?C=D", https("www.example.com", 8443n, "/A/B?C=D"))),
    ("mixed case", parses("hTtP://ExAmPlE.cOm", http("example.com", 80n, "/"))),
    # IPv4
    ("ipv4 host", parses("http://192.168.1.10:8000/x", http("192.168.1.10", 8000n, "/x"))),
    ("is_ipv4 yes", U.is_ipv4("0.0.0.0") && U.is_ipv4("255.255.255.255") && U.is_ipv4("127.0.0.1")),
    ("is_ipv4 no", Bool.not(U.is_ipv4("256.0.0.1")) && Bool.not(U.is_ipv4("1.2.3"))
      && Bool.not(U.is_ipv4("1.2.3.4.5")) && Bool.not(U.is_ipv4("01.2.3.4"))
      && Bool.not(U.is_ipv4("1.2.3.99999999999999999999")) && Bool.not(U.is_ipv4(""))
      && Bool.not(U.is_ipv4("a.b.c.d")) && Bool.not(U.is_ipv4("1.2.3.4."))),
    # numeric hosts that inet_aton would reinterpret (octal / hex / short forms)
    ("ambiguous ipv4 decimal", fails_with("http://2130706433:47321/echo", "ambiguous IPv4 address")
      && fails_with("http://4294967295/", "ambiguous IPv4 address")
      && fails_with("http://0/", "ambiguous IPv4 address")
      && fails_with("http://99999999999999999999999999/", "ambiguous IPv4 address")),
    ("ambiguous ipv4 short", fails_with("http://127.1/", "ambiguous IPv4 address")
      && fails_with("http://127.0.1/", "ambiguous IPv4 address")
      && fails_with("http://1.2.3.4.5/", "ambiguous IPv4 address")
      && fails_with("http://a.1/", "ambiguous IPv4 address")),
    ("ambiguous ipv4 octal", fails_with("http://010.0.0.1/", "ambiguous IPv4 address")
      && fails_with("http://0177.0.0.1/", "ambiguous IPv4 address")
      && fails_with("http://00.0.0.0/", "ambiguous IPv4 address")
      && fails_with("http://127.0.0.01/", "ambiguous IPv4 address")),
    ("ambiguous ipv4 hex", fails_with("http://0x7f.1:47321/echo", "ambiguous IPv4 address")
      && fails_with("http://0xffffffff/", "ambiguous IPv4 address")
      && fails_with("HTTP://0X7F.0.0.1/", "ambiguous IPv4 address")
      && fails_with("http://1.0x/", "ambiguous IPv4 address")
      && fails_with("https://0x7f000001:443/", "ambiguous IPv4 address")),
    ("ambiguous ipv4 octet past 255", fails_with("http://256.0.0.1/", "ambiguous IPv4 address")
      && fails_with("http://1.2.3.99999999999999999999/", "ambiguous IPv4 address")),
    ("ambiguous ipv4 not ok", Bool.not(U.ok(http("2130706433", 80n, "/")))
      && Bool.not(U.ok(http("0x7f.1", 80n, "/"))) && Bool.not(U.host_ok("010.0.0.1"))),
    ("numeric-looking names pass", parses("http://a1.b2/", http("a1.b2", 80n, "/"))
      && parses("http://0x.com/", http("0x.com", 80n, "/"))
      && parses("http://1a/", http("1a", 80n, "/"))
      && parses("http://0xg/", http("0xg", 80n, "/"))
      && parses("http://1.2.3.4.example/", http("1.2.3.4.example", 80n, "/"))
      && parses("http://127.0.0.1./", http("127.0.0.1.", 80n, "/"))),
    ("canonical ipv4 passes", parses("http://0.0.0.0/", http("0.0.0.0", 80n, "/"))
      && parses("https://255.255.255.255:65535/", https("255.255.255.255", 65535n, "/"))
      && rt(http("10.0.0.1", 8080n, "/x"))),
    # query, fragment
    ("query no path", parses("http://h?q=1", http("h", 80n, "/?q=1"))),
    ("query no path port", parses("http://h:81?q", http("h", 81n, "/?q"))),
    ("fragment dropped", parses("http://h/p?q#frag", http("h", 80n, "/p?q"))),
    ("bare fragment", parses("http://h#frag", http("h", 80n, "/"))),
    ("fragment with junk", parses("http://h/p#a b\u{e9}", http("h", 80n, "/p"))),
    # rejected forms
    ("userinfo", fails_with("http://user@h/", "userinfo is not supported")),
    ("userinfo pass", fails_with("http://user:pass@h:8080/", "userinfo is not supported")),
    ("ipv6", fails_with("http://[::1]/", "IPv6 literals are not supported")),
    ("ipv6 port", fails_with("http://[2001:db8::1]:8080/", "IPv6 literals are not supported")),
    ("empty host", fails_with("http:///p", "empty host") && fails_with("http://", "empty host")
      && fails_with("https://:443/", "empty host")),
    ("space in target", fails_with("http://h/a b", "bad char in target")),
    ("space in query", fails_with("http://h?a=b c", "bad char in target")),
    ("crlf in target", fails_with("http://h/\r\nHost: evil", "bad char in target")),
    ("space in host", fails_with("http://h h/", "bad host")),
    ("non-ascii host", fails_with("http://b\u{fc}cher.de/", "bad host")),
    ("non-ascii target", fails_with("http://h/\u{1f600}", "bad char in target")
      && fails_with("http://h/caf\u{e9}", "bad char in target")),
    ("non-byte host", fails_with("http://h\u{100}/", "bad host")),
    ("scheme", fails_with("ftp://h/", "unsupported scheme") && fails_with("", "unsupported scheme")
      && fails_with("example.com/x", "unsupported scheme")),
    ("separator", fails_with("http:/h", "expected :// after the scheme")
      && fails_with("http:h", "expected :// after the scheme")),
    ("all bad chars fail", fails("http://h/\u{7f}") && fails("http://h/\t") && fails("http://h/\u{0}")),
    # show / host_header
    ("show default", String.eq(U.show(http("h", 80n, "/")), "http://h/")),
    ("show port", String.eq(U.show(https("h", 65535n, "/x")), "https://h:65535/x")),
    ("host_header", String.eq(U.host_header(http("h", 80n, "/")), "h")
      && String.eq(U.host_header(https("h", 8443n, "/")), "h:8443")
      && String.eq(U.host_header(http("h", 443n, "/")), "h:443")),
    # ok
    ("ok", U.ok(http("h", 65535n, "/")) && Bool.not(U.ok(http("h", 65536n, "/")))
      && Bool.not(U.ok(http("h", 0n, "/"))) && Bool.not(U.ok(http("H", 80n, "/")))
      && Bool.not(U.ok(http("h", 80n, "x"))) && Bool.not(U.ok(http("h", 80n, "/#")))),
    # roundtrips
    ("roundtrip basic", rt(http("h", 80n, "/")) && rt(https("example.com", 443n, "/")) && rt(http("h", 443n, "/"))
      && rt(https("h", 80n, "/")) && rt(http("127.0.0.1", 65535n, "/?")) && rt(https("a-b.c", 1n, "//?//"))),
    ("roundtrip target chars", rt(http("x.y", 8080n, "/!$&'()*+,;=:@[]{}|\\^`~\"<>%?/?"))),
    ("roundtrip port sweep", port_sweep(256n, 65535n, 255n)),
    ("roundtrip long target", rt(http("h", 80n, "/" ++ rep(4000n, 'a')))),
    ("roundtrip long host", rt(https(rep(2000n, 'a') ++ ".com", 8443n, "/"))),
    ("long target fragment", parses("http://h/" ++ rep(3000n, 'b') ++ "#" ++ rep(3000n, 'c'),
      http("h", 80n, "/" ++ rep(3000n, 'b'))))
  ]

def report(xs: List<(String & Bool)>, fails: Nat) -> IO(Unit):
  match xs:
    case Nil{}:
      match fails:
        case 0n:
          IO.print("ALL PASS")
        case 1n+p:
          IO.print("SOME FAIL: " ++ Nat.show(1n+p))
    case Con{c, t}:
      match c:
        case (name, ok):
          match ok:
            case True{}:
              do IO<Unit>:
                IO.print("PASS " ++ name)
                report(t, fails)
            case False{}:
              do IO<Unit>:
                IO.print("FAIL " ++ name)
                report(t, 1n+fails)

def main() -> IO(Unit):
  report(cases(), 0n)
