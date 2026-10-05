import Base
import ../src/message.bend as M
import ../src/url.bend as U

# Checker-evaluated tests for url.bend: `bend tests/url_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass. The checker evaluates
# Nat in unary, so ports here stay below ~10000; ports 65535 / 65536 and huge
# digit strings are covered at runtime by tests/url_run.bend.

def R() -> Type:
  Result<&2, &2, M.Error, M.Url>

def url(s: M.Scheme, h: String, p: Nat, t: String) -> M.Url:
  M.Url{s, h, p, t}

def http(h: String, p: Nat, t: String) -> R():
  Done{M.Url{M.Http{}, h, p, t}}

def https(h: String, p: Nat, t: String) -> R():
  Done{M.Url{M.Https{}, h, p, t}}

def bad(reason: String) -> R():
  Fail{M.BadUrl{reason}}

# default ports
def t_default_ports_1() ->
  {U.default_port(M.Http{}) == 80n : Nat} &
  {U.default_port(M.Https{}) == 443n : Nat} &
  {U.parse("http://example.com") == http("example.com", 80n, "/") : R()} &
  {U.parse("https://example.com/") == https("example.com", 443n, "/") : R()}:
  ({==}, {==}, {==}, {==})

# explicit ports
def t_explicit_ports_1() ->
  {U.parse("https://h:443/") == https("h", 443n, "/") : R()} &
  {U.parse("http://h:80") == http("h", 80n, "/") : R()} &
  {U.parse("https://h:80/x") == https("h", 80n, "/x") : R()} &
  {U.parse("http://h:1/") == http("h", 1n, "/") : R()} &
  {U.parse("http://h:0081/") == http("h", 81n, "/") : R()}:
  ({==}, {==}, {==}, {==}, {==})

# a 4-digit port on its own (the checker's unary Nat is deep)
def t_explicit_ports_8080() ->
  {U.parse("http://example.com:8080/a/b?c=d") == http("example.com", 8080n, "/a/b?c=d") : R()}:
  {==}

# a 4-digit port on its own (the checker's unary Nat is deep)
def t_explicit_ports_9999() ->
  {U.parse("http://h:9999/") == http("h", 9999n, "/") : R()}:
  {==}

# uppercase scheme / host (path case kept)
def t_uppercase_1() ->
  {U.parse("HTTP://EXAMPLE.COM/Path") == http("example.com", 80n, "/Path") : R()} &
  {U.parse("HtTpS://Mixed-Case.Org?Q=A") == https("mixed-case.org", 443n, "/?Q=A") : R()}:
  ({==}, {==})

# IPv4 hosts
def t_ipv4_hosts_1() ->
  {U.parse("http://127.0.0.1:3000/x") == http("127.0.0.1", 3000n, "/x") : R()} &
  {U.parse("https://10.0.0.1") == https("10.0.0.1", 443n, "/") : R()}:
  ({==}, {==})

# query without path, fragments dropped
def t_query_fragment_1() ->
  {U.parse("http://h?q") == http("h", 80n, "/?q") : R()} &
  {U.parse("http://h:81?q=1&r=2") == http("h", 81n, "/?q=1&r=2") : R()} &
  {U.parse("http://h?q#f") == http("h", 80n, "/?q") : R()} &
  {U.parse("http://h/p#frag") == http("h", 80n, "/p") : R()} &
  {U.parse("http://h#frag") == http("h", 80n, "/") : R()} &
  {U.parse("http://h:82#") == http("h", 82n, "/") : R()} &
  {U.parse("http://h/p?q#f#g") == http("h", 80n, "/p?q") : R()} &
  {U.parse("http://h/a/b/../c;p=1?x=[1]&y=@:/") == http("h", 80n, "/a/b/../c;p=1?x=[1]&y=@:/") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# query without path, fragments dropped (cont.)
def t_query_fragment_2() ->
  {U.parse("http://h?") == http("h", 80n, "/?") : R()} &
  {U.parse("http://h/") == http("h", 80n, "/") : R()}:
  ({==}, {==})

# userinfo
def t_userinfo_1() ->
  {U.parse("http://user@h/") == bad("userinfo is not supported") : R()} &
  {U.parse("http://user:pass@h:8080/") == bad("userinfo is not supported") : R()} &
  {U.parse("http://@h") == bad("userinfo is not supported") : R()}:
  ({==}, {==}, {==})

# IPv6
def t_ipv6_1() ->
  {U.parse("http://[::1]/") == bad("IPv6 literals are not supported") : R()} &
  {U.parse("http://[::1]:8080/") == bad("IPv6 literals are not supported") : R()} &
  {U.parse("http://h]/") == bad("IPv6 literals are not supported") : R()}:
  ({==}, {==}, {==})

# empty host
def t_empty_host_1() ->
  {U.parse("http://") == bad("empty host") : R()} &
  {U.parse("http:///x") == bad("empty host") : R()} &
  {U.parse("http://:80/") == bad("empty host") : R()} &
  {U.parse("http://?q") == bad("empty host") : R()}:
  ({==}, {==}, {==}, {==})

# empty / bad ports
def t_empty_bad_ports_1() ->
  {U.parse("http://h:/") == bad("empty port") : R()} &
  {U.parse("http://h:") == bad("empty port") : R()} &
  {U.parse("http://h:0/") == bad("port out of range") : R()} &
  {U.parse("http://h:000/") == bad("port out of range") : R()} &
  {U.parse("http://h:8a/") == bad("bad port") : R()} &
  {U.parse("http://h:-1/") == bad("bad port") : R()} &
  {U.parse("http://h:+80/") == bad("bad port") : R()} &
  {U.parse("http://h: 80/") == bad("bad port") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# empty / bad ports (cont.)
def t_empty_bad_ports_2() ->
  {U.parse("http://h:80:81/") == bad("bad port") : R()}:
  {==}

# spaces and control chars
def t_spaces_ctl_1() ->
  {U.parse("http://h/a b") == bad("bad char in target") : R()} &
  {U.parse("http://h?a b") == bad("bad char in target") : R()} &
  {U.parse("http://h/\r\nX-Evil: 1") == bad("bad char in target") : R()} &
  {U.parse("http://h/\t") == bad("bad char in target") : R()} &
  {U.parse("http://h a/") == bad("bad host") : R()} &
  {U.parse("http:// h/") == bad("bad host") : R()} &
  {U.parse(" http://h/") == bad("unsupported scheme") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

# non-ASCII
def t_non_ascii_1() ->
  {U.parse("http://h/caf\u{e9}") == bad("bad char in target") : R()} &
  {U.parse("http://h/\u{100}") == bad("bad char in target") : R()} &
  {U.parse("http://ex\u{e4}mple.com/") == bad("bad host") : R()} &
  {U.parse("http://\u{c0}/") == bad("bad host") : R()} &
  {U.parse("htt\u{d0}://h/") == bad("unsupported scheme") : R()}:
  ({==}, {==}, {==}, {==}, {==})

# other bad host chars
def t_other_bad_host_chars_1() ->
  {U.parse("http://h_x/") == bad("bad host") : R()} &
  {U.parse("http://h\\x/") == bad("bad host") : R()} &
  {U.parse("http://h!/") == bad("bad host") : R()}:
  ({==}, {==}, {==})

# schemes and the separator
def t_schemes_1() ->
  {U.parse("ftp://h/") == bad("unsupported scheme") : R()} &
  {U.parse("httpx://h/") == bad("unsupported scheme") : R()} &
  {U.parse("") == bad("unsupported scheme") : R()} &
  {U.parse("example.com") == bad("unsupported scheme") : R()} &
  {U.parse("http") == bad("expected :// after the scheme") : R()} &
  {U.parse("http:") == bad("expected :// after the scheme") : R()} &
  {U.parse("http:/h") == bad("expected :// after the scheme") : R()} &
  {U.parse("http:h/x") == bad("expected :// after the scheme") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# schemes and the separator (cont.)
def t_schemes_2() ->
  {U.parse("http:\\\\h/") == bad("expected :// after the scheme") : R()}:
  {==}

# host_ok / target_ok
def t_host_ok_target_ok_1() ->
  {U.host_ok("a-b.c9") == True{} : Bool} &
  {U.host_ok("") == False{} : Bool} &
  {U.host_ok("A") == False{} : Bool} &
  {U.host_ok("a b") == False{} : Bool} &
  {U.host_ok("a:1") == False{} : Bool} &
  {U.host_ok("a/") == False{} : Bool} &
  {U.host_ok("a#") == False{} : Bool} &
  {U.host_ok("a?") == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# host_ok / target_ok (cont.)
def t_host_ok_target_ok_2() ->
  {U.target_ok("/") == True{} : Bool} &
  {U.target_ok("/a?b=c&d=[e]@f:g;h") == True{} : Bool} &
  {U.target_ok("") == False{} : Bool} &
  {U.target_ok("a/") == False{} : Bool} &
  {U.target_ok("?q") == False{} : Bool} &
  {U.target_ok("/a#b") == False{} : Bool} &
  {U.target_ok("/a b") == False{} : Bool} &
  {U.target_ok("/\u{7f}") == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# is_ipv4
def t_is_ipv4_1() ->
  {U.is_ipv4("1.2.3.4") == True{} : Bool} &
  {U.is_ipv4("0.0.0.0") == True{} : Bool} &
  {U.is_ipv4("255.255.255.255") == True{} : Bool} &
  {U.is_ipv4("192.168.10.200") == True{} : Bool} &
  {U.is_ipv4("256.1.1.1") == False{} : Bool} &
  {U.is_ipv4("1.2.3.999") == False{} : Bool} &
  {U.is_ipv4("1.2.3") == False{} : Bool} &
  {U.is_ipv4("1.2.3.4.5") == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# is_ipv4 (cont.)
def t_is_ipv4_2() ->
  {U.is_ipv4("1.2.3.4.") == False{} : Bool} &
  {U.is_ipv4(".1.2.3") == False{} : Bool} &
  {U.is_ipv4("1..2.3") == False{} : Bool} &
  {U.is_ipv4("01.2.3.4") == False{} : Bool} &
  {U.is_ipv4("1.2.3.00") == False{} : Bool} &
  {U.is_ipv4("-1.2.3.4") == False{} : Bool} &
  {U.is_ipv4("a.b.c.d") == False{} : Bool} &
  {U.is_ipv4("1.2.3.4 ") == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# is_ipv4 (cont.)
def t_is_ipv4_3() ->
  {U.is_ipv4("") == False{} : Bool} &
  {U.is_ipv4("example.com") == False{} : Bool}:
  ({==}, {==})

# numeric hosts: a host whose last label is a number must be a canonical
# dotted quad, else inet_aton would read it as some other address
def t_ambiguous_ipv4_1() ->
  {U.parse("http://2130706433/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://127.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://0x7f.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://010.0.0.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://0177.0.0.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://00.0.0.0/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://0/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://4294967295:80/x") == bad("ambiguous IPv4 address") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# numeric hosts (cont.)
def t_ambiguous_ipv4_2() ->
  {U.parse("http://0xffffffff/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://0X7F.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://1.2.3.4.5/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://a.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://1.0x/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://256.0.0.1/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://0x7f.1:0/") == bad("ambiguous IPv4 address") : R()} &
  {U.parse("http://1_2/") == bad("bad host") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# numeric-looking names and canonical quads pass
def t_ambiguous_ipv4_3() ->
  {U.parse("http://127.0.0.1/") == http("127.0.0.1", 80n, "/") : R()} &
  {U.parse("http://example.com/") == http("example.com", 80n, "/") : R()} &
  {U.parse("http://a1.b2/") == http("a1.b2", 80n, "/") : R()} &
  {U.parse("http://0x.com/") == http("0x.com", 80n, "/") : R()} &
  {U.parse("http://1a/") == http("1a", 80n, "/") : R()} &
  {U.parse("http://0xg/") == http("0xg", 80n, "/") : R()} &
  {U.parse("http://127.0.0.1./") == http("127.0.0.1.", 80n, "/") : R()} &
  {U.parse("http://1.2.3.4.example/") == http("1.2.3.4.example", 80n, "/") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# host_ok and ok agree with parse on numeric hosts (law 17's premise)
def t_ambiguous_ipv4_4() ->
  {U.host_ok("2130706433") == False{} : Bool} &
  {U.host_ok("127.1") == False{} : Bool} &
  {U.host_ok("0x7f.1") == False{} : Bool} &
  {U.host_ok("010.0.0.1") == False{} : Bool} &
  {U.host_ok("127.0.0.1") == True{} : Bool} &
  {U.host_ok("a1.b2") == True{} : Bool} &
  {U.ok(url(M.Http{}, "127.1", 80n, "/")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "10.0.0.1", 80n, "/")) == True{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# ok
def t_ok_1() ->
  {U.ok(url(M.Http{}, "h", 80n, "/")) == True{} : Bool} &
  {U.ok(url(M.Https{}, "a.b", 1n, "/x?y")) == True{} : Bool} &
  {U.ok(url(M.Http{}, "h", 0n, "/")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "h", 65536n, "/")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "", 80n, "/")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "H", 80n, "/")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "h", 80n, "")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "h", 80n, "x")) == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# ok (cont.)
def t_ok_2() ->
  {U.ok(url(M.Http{}, "h", 80n, "/#f")) == False{} : Bool} &
  {U.ok(url(M.Http{}, "h", 80n, "/a b")) == False{} : Bool}:
  ({==}, {==})

# show / host_header
def t_show_host_header_1() ->
  {U.show(url(M.Http{}, "h", 80n, "/")) == "http://h/" : String} &
  {U.show(url(M.Https{}, "h", 443n, "/a?b")) == "https://h/a?b" : String} &
  {U.show(url(M.Http{}, "h", 8080n, "/x")) == "http://h:8080/x" : String} &
  {U.show(url(M.Https{}, "h", 80n, "/")) == "https://h:80/" : String} &
  {U.show(url(M.Http{}, "h", 443n, "/")) == "http://h:443/" : String} &
  {U.host_header(url(M.Http{}, "example.com", 80n, "/")) == "example.com" : String} &
  {U.host_header(url(M.Https{}, "example.com", 443n, "/")) == "example.com" : String} &
  {U.host_header(url(M.Http{}, "example.com", 8080n, "/")) == "example.com:8080" : String}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# show / host_header (cont.)
def t_show_host_header_2() ->
  {U.host_header(url(M.Https{}, "10.0.0.1", 80n, "/")) == "10.0.0.1:80" : String}:
  {==}

# roundtrip: ok(u) => parse(show(u)) == Done{u}
def t_roundtrip_1() ->
  {U.parse(U.show(url(M.Http{}, "h", 80n, "/"))) == http("h", 80n, "/") : R()} &
  {U.parse(U.show(url(M.Https{}, "example.com", 443n, "/"))) == https("example.com", 443n, "/") : R()} &
  {U.parse(U.show(url(M.Https{}, "h", 80n, "/x"))) == https("h", 80n, "/x") : R()} &
  {U.parse(U.show(url(M.Http{}, "h", 443n, "/"))) == http("h", 443n, "/") : R()} &
  {U.parse(U.show(url(M.Http{}, "127.0.0.1", 1n, "/?"))) == http("127.0.0.1", 1n, "/?") : R()} &
  {U.parse(U.show(url(M.Http{}, "x", 81n, "//?//"))) == http("x", 81n, "//?//") : R()}:
  ({==}, {==}, {==}, {==}, {==}, {==})

# a 4-digit port on its own (the checker's unary Nat is deep)
def t_roundtrip_8080() ->
  {U.parse(U.show(url(M.Http{}, "example.com", 8080n, "/a/b?c=d"))) == http("example.com", 8080n, "/a/b?c=d") : R()}:
  {==}

# a 4-digit port on its own
def t_roundtrip_9999() ->
  {U.parse(U.show(url(M.Https{}, "a-b.c-d.e9", 9999n, "/p;q?r=[s]&t=@:/u"))) == https("a-b.c-d.e9", 9999n, "/p;q?r=[s]&t=@:/u") : R()}:
  {==}

# roundtrip: ok(u) => parse(show(u)) == Done{u} (cont.)
def t_roundtrip_2() ->
  {U.parse(U.show(url(M.Http{}, "-", 1000n, "/~!$&'()*+,"))) == http("-", 1000n, "/~!$&'()*+,") : R()}:
  {==}

# the roundtrip cases above all satisfy the premise ok(u)
def t_roundtrip_premises() ->
  {U.ok(url(M.Http{}, "h", 80n, "/")) == True{} : Bool} &
  {U.ok(url(M.Https{}, "example.com", 443n, "/")) == True{} : Bool} &
  {U.ok(url(M.Http{}, "example.com", 8080n, "/a/b?c=d")) == True{} : Bool} &
  {U.ok(url(M.Https{}, "h", 80n, "/x")) == True{} : Bool} &
  {U.ok(url(M.Http{}, "h", 443n, "/")) == True{} : Bool} &
  {U.ok(url(M.Http{}, "127.0.0.1", 1n, "/?")) == True{} : Bool} &
  {U.ok(url(M.Https{}, "a-b.c-d.e9", 9999n, "/p;q?r=[s]&t=@:/u")) == True{} : Bool} &
  {U.ok(url(M.Http{}, "x", 81n, "//?//")) == True{} : Bool} &
  {U.ok(url(M.Http{}, "-", 1000n, "/~!$&'()*+,")) == True{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# and the other way for canonical text: show(parse(s)) == s
def t_show_parse_1() ->
  {U.show(Result.default(&2, &2, M.Error, M.Url, U.parse("https://h:8443/a?b"), url(M.Http{}, "", 0n, ""))) == "https://h:8443/a?b" : String}:
  {==}

# Every group above is checked when this file is checked; main is a marker.
def main() -> Unit:
  Unit{}
