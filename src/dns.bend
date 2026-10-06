import Base
import ../../dns/main.bend as D
import ./message.bend as M
import ./url.bend as U
import ./headers.bend as H

# Adapter to the sibling bender-dns package's native IPv4 resolver.
# None loads /etc/resolv.conf and /etc/hosts; Some uses the caller's config.
# HTTP keeps its numeric-host checks before asking DNS, including lookup().

def Dns.error.kind(kind: D.Dns.ErrorKind(), +e: D.Dns.Error(), host: String) -> M.Error:
  match kind:
    case D.Timeout{}:
      M.Timeout{}
    case D.NoData{}:
      M.NoAddress{host}
    case _:
      M.Dns{Maybe.default(&2, U32, D.Dns.Error.code(e), 0), D.Dns.Error.show(e)}

def Dns.error(+e: D.Dns.Error(), host: String) -> M.Error:
  Dns.error.kind(D.Dns.Error.kind(e), e, host)

def Dns.answer(r: Result<&2, &2, D.Dns.Error(), List<&2, String>>, host: String) ->
  Result<&2, &2, M.Error, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{Dns.error(e, host)}
    case Done{ips}:
      Done{ips}

def Dns.configured(r: Result<&2, &2, D.Dns.Error(), D.Dns.Config()>, +host: String) ->
  IO(Result<&2, &2, M.Error, List<&2, String>>):
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, M.Error, List<&2, String>>, Fail{Dns.error(e, host)})
    case Done{cfg}:
      IO.bind(Result<&2, &2, D.Dns.Error(), List<&2, String>>, Result<&2, &2, M.Error, List<&2, String>>,
        D.Dns.lookup_ipv4(cfg, host), r => IO.pure(Result<&2, &2, M.Error, List<&2, String>>, Dns.answer(r, host)))

def Dns.native(cfg: Maybe<&2, D.Dns.Config()>, host: String) ->
  IO(Result<&2, &2, M.Error, List<&2, String>>):
  match cfg:
    case Some{c}:
      Dns.configured(Done{c}, host)
    case None{}:
      IO.bind(Result<&2, &2, D.Dns.Error(), D.Dns.Config()>, Result<&2, &2, M.Error, List<&2, String>>,
        D.Dns.system(), r => Dns.configured(r, host))

def Dns.checked(bad: Bool, literal: Bool, cfg: Maybe<&2, D.Dns.Config()>, +host: String) ->
  IO(Result<&2, &2, M.Error, List<&2, String>>):
  match bad literal:
    case True{} _:
      IO.pure(Result<&2, &2, M.Error, List<&2, String>>,
        Fail{M.Dns{22, "invalid or ambiguous host name"}})
    case False{} True{}:
      IO.pure(Result<&2, &2, M.Error, List<&2, String>>, Done{[host]})
    case False{} False{}:
      Dns.native(cfg, host)

def Dns.lookup_with(cfg: Maybe<&2, D.Dns.Config()>, +host: String) ->
  IO(Result<&2, &2, M.Error, List<&2, String>>):
  +literal = U.is_ipv4(host)
  +bad = String.eq(host, "") || String.contains(host, "\0")
    || (Bool.not(literal) && U.ends_in_number(H.lower(host)))
  Dns.checked(bad, literal, cfg, host)

def Dns.lookup(host: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  Dns.lookup_with(None{}, host)
