import Base
import ../main.bend as P
import ../../dns/main.bend as D

# Invoked by cli_test.sh with the local DNS server's ephemeral port.
def report(ok: Bool, label: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ label)
    case False{}:
      IO.die(Unit, 1, "FAIL " ++ label)

def answer(r: Result<&2, &2, P.Http.Error(), String>, want: String, label: String) -> IO(Unit):
  match r:
    case Done{ip}:
      report(String.eq(ip, want), label)
    case Fail{e}:
      IO.die(Unit, 1, "FAIL " ++ label ++ ": " ++ P.Http.Error.show(e))

def error_kind(k: P.Http.ErrorKind()) -> String:
  match k:
    case P.NoAddress{}:
      "no-address"
    case P.Dns{}:
      "dns"
    case P.Timeout{}:
      "timeout"
    case P.BadUrl{}:
      "bad-url"
    case P.BadRequest{}:
      "bad-request"
    case _:
      "other"

def failure(r: Result<&2, &2, P.Http.Error(), String>, want: String, label: String) -> IO(Unit):
  match r:
    case Done{ip}:
      IO.die(Unit, 1, "FAIL " ++ label ++ ": unexpected " ++ ip)
    case Fail{e}:
      report(String.eq(error_kind(P.Http.Error.kind(e)), want), label)

def tests(+port: Nat) -> IO(Unit):
  +dns = D.Dns.with_attempts(D.Dns.with_port(D.Dns.with_timeout(
    D.Dns.with_servers(D.Dns.default_config(), ["127.0.0.1"]), 1000n), port), 1n)
  +cfg = P.Http.with_dns(P.Http.default_config(), dns)
  +hosts = P.Http.with_host(P.Http.with_timeout(P.Http.with_max_bytes(cfg, 1000n), 2000n), "x.test", "127.0.0.2")
  +search = P.Http.with_dns(cfg, D.Dns.with_search(dns, ["test"]))
  +file = P.Http.with_dns(cfg, D.Dns.with_hosts(dns, "127.0.0.3 hosts.test\n"))
  +dead = P.Http.with_dns(cfg, D.Dns.with_servers(dns, Nil{}))
  do IO<Unit>:
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(cfg, "x.test"), r => answer(r, "127.0.0.1", "custom native resolver"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(hosts, "X.TEST"), r => answer(r, "127.0.0.2", "HTTP hosts precedence; setters retain DNS"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(file, "HOSTS.TEST"), r => answer(r, "127.0.0.3", "DNS hosts file"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(search, "x"), r => answer(r, "127.0.0.1", "DNS search suffix"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(cfg, "alias.test"), r => answer(r, "127.0.0.1", "CNAME requery"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(dead, "127.0.0.4"), r => answer(r, "127.0.0.4", "literal bypasses DNS"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(dead, "none.test"), r => failure(r, "dns", "DNS failure mapping"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(cfg, "nodata.test"), r => failure(r, "no-address", "NODATA mapping"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(cfg, "missing.test"), r => failure(r, "dns", "NXDOMAIN mapping"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(cfg, "127.1"), r => failure(r, "bad-url", "ambiguous host refused"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(P.Http.with_host(cfg, "bad.test", "127.1"), "bad.test"), r => failure(r, "bad-request", "invalid override refused"))
    IO.bind(Result<&2, &2, P.Http.Error(), String>, Unit, P.Http.resolve(P.Http.with_timeout(cfg, 100n), "slow.test"), r => failure(r, "timeout", "whole DNS lookup deadline"))
    IO.die(Unit, 0, "")

def args_(args: List<String>) -> IO(Unit):
  match args:
    case Con{s, Nil{}}:
      tests(Maybe.default(&2, Nat, Nat.read(s), 0n))
    case _:
      IO.die(Unit, 1, "expected DNS port")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    args_(List.tail(&1, String, args))
