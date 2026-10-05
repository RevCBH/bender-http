import Base
import ./bytes.bend as B
import ./message.bend as M
import ./decode.bend as D
import ./tls.bend as T

# The wire: one request out, one response back, over a fresh connection.
#
# - `plain` speaks HTTP over Base's TCP: connect, send the request bytes, and
#   read 64 KiB at a time, feeding each read to the decoder (`D.feed`) until
#   it is done (complete or failed) or the peer closes (an empty read); then
#   `D.finish`. A response framed by Content-Length or chunked is complete
#   before the close, so the reader stops there without waiting for it.
# - `tls` does the same over OpenSSL (foreign): `Tls.open` connects,
#   verifies and sends; each `Tls.recv` is fed to the decoder until it is
#   done or the stream ends; `Tls.close` always follows. A close without
#   close_notify is accepted only when the HTTP framing shows the message
#   complete (RFC 9112 §9.8).
#
# Both take the IPv4 address to connect to (the caller resolved the name) and
# answer the decoded response or why there is none. This file imports foreign
# code (tls.bend), so nothing a law imports may import it.

# Clamps
# ------

# A Nat as a U32 for a Base or foreign effect, saturating at 2^32-1 (U32's
# conversion would wrap, and a wrapped port or limit could be valid).
def u32(n: Nat) -> U32:
  U32.from_nat(Nat.min(n, 4294967295n))

# A port for TCP.connect / Tls.open: anything past 65535 becomes 65536,
# which both refuse with EINVAL (instead of wrapping into a valid port).
def port_u32(p: Nat) -> U32:
  U32.from_nat(Nat.min(p, 65536n))

# Racing an action against a deadline
# -----------------------------------
#
# `within(A, ms, act)` is IO.within with one difference: its timer stops once
# the action wins. Base's IO.within sleeps the whole `ms` in a forked
# computation that nobody can cancel, and a program ends only when every
# computation is done, so each read under IO.within(30000, ..) would keep the
# program alive 30 s after the response arrived. Here the timer sleeps in
# slices of 100 ms and, after each, sends a Tick on the race's channel; once
# the race is decided the channel is closed, the next Tick's send answers
# False, and the timer ends (at most 100 ms later).
#
# What neither version can do is cancel the action: Base has no way to abort
# a blocked recv or connect. When the deadline wins, the action keeps running
# (and keeps the program alive) until the peer acts or the OS gives up, and
# whatever it then produces (a Socket among it) is dropped unclosed. That is
# the limit of a timeout over Base's TCP; Tls.open / Tls.recv time out on
# their own (and do cancel). client.bend also uses `within` for the name
# lookup, with the same limit.

type Race<-A: Type> is Type:
  Won{value: A}
  Tick{}
  Late{}

def SLICE() -> Nat:
  100n

# The timer's next slice, once its Tick was taken (True) or refused (False:
# the race is over).
def timer.next(open: Bool, rest: IO(Bool)) -> IO(Bool):
  match open:
    case True{}:
      rest
    case False{}:
      IO.pure(Bool, False{})

# `n` slices of SLICE ms, each followed by a Tick, then `r` ms and Late.
def timer(-A: Type, n: Nat, r: Nat, +c: Chan(Race<A>)) -> IO(Bool):
  match n:
    case 0n:
      do IO<Bool>:
        IO.sleep(u32(r))
        Chan.send(Race<A>, c, Late{})
    case 1n+p:
      do IO<Bool>:
        IO.sleep(u32(SLICE()))
        open : Bool <- Chan.send(Race<A>, c, Tick{})
        timer.next(open, timer(A, p, r, c))

def join.end(-A: Type, +c: Chan(Race<A>), x: Maybe<&1, A>) -> IO(Maybe<&1, A>):
  do IO<Maybe<&1, A>>:
    Chan.close(Race<A>, c)
    return x

def join.got(-A: Type, got: Maybe<&1, Race<A>>, +c: Chan(Race<A>), rest: IO(Maybe<&1, A>)) ->
  IO(Maybe<&1, A>):
  match got:
    case None{}:
      IO.pure(Maybe<&1, A>, None{})
    case Some{Won{x}}:
      join.end(A, c, Some{x})
    case Some{Tick{}}:
      rest
    case Some{Late{}}:
      join.end(A, c, None{})

# Waits for Won or Late, skipping Ticks; the fuel covers every message the
# timer can send (its ticks and Late) plus the action's one.
def join(-A: Type, fuel: Nat, +c: Chan(Race<A>)) -> IO(Maybe<&1, A>):
  match fuel:
    case 0n:
      join.end(A, c, None{})
    case 1n+p:
      IO.bind(Maybe<&1, Race<A>>, Maybe<&1, A>, Chan.recv(Race<A>, c),
        got => join.got(A, got, c, join(A, p, c)))

def race.go(-A: Type, n: Nat, r: Nat, act: IO(A), +c: Chan(Race<A>)) -> IO(Maybe<&1, A>):
  +slices = n
  do IO<Maybe<&1, A>>:
    IO.spawn(Bool, IO.bind(A, Bool, act, x => Chan.send(Race<A>, c, Won{x})))
    IO.spawn(Bool, timer(A, slices, r, c))
    join(A, 3n+slices, c)

# `nr` is the deadline as (whole slices, remaining ms).
def race(-A: Type, nr: Nat & Nat, act: IO(A)) -> IO(Maybe<&1, A>):
  (n, r) = nr
  IO.bind(Chan(Race<A>), Maybe<&1, A>, Chan.new(Race<A>, 1), c => race.go(A, n, r, act, c))

# Some{result} if `act` finishes within `ms` milliseconds, else None; 0 means
# no limit.
def within(-A: Type, ms: Nat, act: IO(A)) -> IO(Maybe<&1, A>):
  match ms:
    case 0n:
      IO.bind(A, Maybe<&1, A>, act, x => IO.pure(Maybe<&1, A>, Some{x}))
    case 1n+p:
      race(A, Nat.divmod(1n+p, SLICE()), act)

# Plain HTTP over Base's TCP
# --------------------------

def fail(e: M.Error) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  IO.pure(Result<&2, &2, M.Error, M.Decoded>, Fail{e})

# The decoder's verdict at the end of input, as the client's error.
def verdict(r: Result<&2, &2, M.ParseError, M.Decoded>) -> Result<&2, &2, M.Error, M.Decoded>:
  match r:
    case Fail{e}:
      Fail{M.Parse{e}}
    case Done{d}:
      Done{d}

# Closes the socket, then answers the decoder's verdict on s.
def close_with(sock: Socket, s: D.State) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  do IO<Result<&2, &2, M.Error, M.Decoded>>:
    Socket.close(sock)
    return verdict(D.finish(s))

def close_fail(sock: Socket, e: M.Error) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  do IO<Result<&2, &2, M.Error, M.Decoded>>:
    Socket.close(sock)
    return Fail{e}

# After a productive read: stop when the decoder is done, else read again.
def fed(done: Bool, sock: Socket, s: D.State, more: Socket -> D.State -> IO(Result<&2, &2, M.Error, M.Decoded>)) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  match done:
    case True{}:
      close_with(sock, s)
    case False{}:
      more(sock, s)

# What one read brought: an empty read is the peer's close (the end of
# input); otherwise feed the bytes to the decoder.
def got(xs: List<&2, U32>, sock: Socket, s: D.State, more: Socket -> D.State -> IO(Result<&2, &2, M.Error, M.Decoded>)) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  match xs:
    case Nil{}:
      close_with(sock, s)
    case Con{h, t}:
      +s2 = D.feed(s, h <> t)
      fed(D.done(s2), sock, s2, more)

# One read's outcome: the deadline passed (the read still holds the socket,
# see `within`), the read failed, or it brought bytes.
def read_got(r: Maybe<&1, Socket & Result<&1, &1, U32 & String, List<&2, U32>>>, s: D.State,
  more: Socket -> D.State -> IO(Result<&2, &2, M.Error, M.Decoded>)) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  match r:
    case None{}:
      fail(M.Timeout{})
    case Some{(sock, res)}:
      match res:
        case Fail{(code, message)}:
          close_fail(sock, M.Io{code, message})
        case Done{xs}:
          got(xs, sock, s, more)

# Reads until the decoder is done or the peer closes. Each productive read
# either finishes the decoder or spends at least one byte of its budget, so
# `fuel` = budget + 2 reads always suffice; running out is reported as the
# end of input.
def read_loop(fuel: Nat, sock: Socket, s: D.State, +ms: Nat) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  match fuel:
    case 0n:
      close_with(sock, s)
    case 1n+p:
      IO.bind(Maybe<&1, Socket & Result<&1, &1, U32 & String, List<&2, U32>>>,
        Result<&2, &2, M.Error, M.Decoded>,
        within(Socket & Result<&1, &1, U32 & String, List<&2, U32>>, ms, TCP.recv_bytes(sock, 65536)),
        r => read_got(r, s, sock2 => s2 => read_loop(p, sock2, s2, ms)))

# The request was sent (or not): on success, read the response.
def sent(r: Maybe<&1, Socket & Result<&1, &1, U32 & String, Unit>>, method: M.Method, +max: Nat, +ms: Nat) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  match r:
    case None{}:
      fail(M.Timeout{})
    case Some{(sock, res)}:
      match res:
        case Fail{(code, message)}:
          close_fail(sock, M.Io{code, message})
        case Done{u}:
          read_loop(2n+max, sock, D.init(method, max), ms)

# Connected (or not): on success, send the whole request.
def connected(r: Maybe<&1, Result<&1, &1, U32 & String, Socket>>, req: List<&2, U32>, method: M.Method,
  max: Nat, +ms: Nat) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  match r:
    case None{}:
      fail(M.Timeout{})
    case Some{res}:
      match res:
        case Fail{(code, message)}:
          fail(M.Connect{code, message})
        case Done{sock}:
          IO.bind(Maybe<&1, Socket & Result<&1, &1, U32 & String, Unit>>,
            Result<&2, &2, M.Error, M.Decoded>,
            within(Socket & Result<&1, &1, U32 & String, Unit>, ms, TCP.send_bytes(sock, req)),
            s => sent(s, method, max, ms))

# One HTTP exchange with ip:port: connect, send `req`, and decode the
# response for `method` with a budget of `max` bytes. The connect, the send
# and each read must each finish within `timeout_ms` (0: no limit), else
# Timeout. The socket is closed on every path except a timeout, where the
# stalled effect still holds it (see `within`).
def plain(ip: String, port: Nat, req: List<&2, U32>, method: M.Method, max: Nat, +timeout_ms: Nat) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  IO.bind(Maybe<&1, Result<&1, &1, U32 & String, Socket>>, Result<&2, &2, M.Error, M.Decoded>,
    within(Result<&1, &1, U32 & String, Socket>, timeout_ms, TCP.connect(ip, port_u32(port))),
    r => connected(r, req, method, max, timeout_ms))

# HTTPS over Tls.open / Tls.recv / Tls.close
# ------------------------------------------
#
# The same reader as `plain`: feed each read to the decoder and stop as soon
# as it is done, so a server that keeps the connection open, resets it after
# the response, or sends bytes past the message costs nothing (the leftover
# is not charged to the budget, and no raw byte cap applies: the decoder's
# budget is the only limit). Every Tls.recv is bounded by the timeout given
# to Tls.open, inside the foreign code, which does cancel.
#
# How the stream ended matters only when the message is not done yet:
# - `[]` (close_notify): the end of input, so `D.finish` decides;
# - ECONNRESET after some bytes (a close without close_notify, or a reset):
#   if the body runs to the close (`D.close_delimited`), the cut may have
#   truncated it (RFC 9112 §9.8: such a body is complete only with a valid
#   closure alert), so the request fails with the Tls error; otherwise the
#   framing shows the message unfinished, which `D.finish` reports as
#   Incomplete (as for a plain close mid-message);
# - any other failure: the Tls error (`tls_error`).

# Tls.exchange's / Tls.open's / Tls.recv's errno, as the client's error.
# Linux values first, macOS second: ETIMEDOUT (110, 60) is a Timeout;
# ECONNREFUSED (111, 61), ENETUNREACH (101, 51) and EHOSTUNREACH (113, 65)
# are a Connect error; EFBIG (27, from Tls.exchange's raw cap) is the
# decoder's TooLarge; everything else (EPROTO for a certificate or name that
# fails verification, ECONNABORTED for any other TLS failure, ECONNRESET,
# ...) is a Tls error.
def tls_error(+code: U32, +message: String) -> M.Error:
  +timeout = U32.is_eq(code, 110) || U32.is_eq(code, 60)
  +refused = U32.is_eq(code, 111) || U32.is_eq(code, 61) || U32.is_eq(code, 101)
    || U32.is_eq(code, 51) || U32.is_eq(code, 113) || U32.is_eq(code, 65)
  +big = U32.is_eq(code, 27)
  Bool.pick(M.Error, timeout, M.Timeout{},
  Bool.pick(M.Error, refused, M.Connect{code, message},
  Bool.pick(M.Error, big, M.Parse{M.TooLarge{}},
  M.Tls{code, message})))

# ECONNRESET (Linux 104, macOS 54).
def is_reset(+code: U32) -> Bool:
  U32.is_eq(code, 104) || U32.is_eq(code, 54)

# Closes the connection, then answers r.
def tls_end(conn: U32, r: Result<&2, &2, M.Error, M.Decoded>) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  do IO<Result<&2, &2, M.Error, M.Decoded>>:
    T.Tls.close(conn)
    return r

# A read failed with code. `cut`: it was a close or reset after some bytes,
# with a framing that shows the message unfinished; the decoder then says
# what is missing (Incomplete). Otherwise the failure itself is the answer.
def tls_cut(cut: Bool, s: D.State, +code: U32, message: String) -> Result<&2, &2, M.Error, M.Decoded>:
  match cut:
    case True{}:
      verdict(D.finish(s))
    case False{}:
      Fail{tls_error(code, message)}

# After a productive read: stop when the decoder is done, else read again.
def tls_fed(done: Bool, +conn: U32, s: D.State, more: D.State -> IO(Result<&2, &2, M.Error, M.Decoded>)) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  match done:
    case True{}:
      tls_end(conn, verdict(D.finish(s)))
    case False{}:
      more(s)

# What one Tls.recv brought. `some`: an earlier read brought bytes.
def tls_got(r: Result<&1, &1, U32 & String, List<&2, U32>>, +conn: U32, +s: D.State, +some: Bool,
  more: D.State -> IO(Result<&2, &2, M.Error, M.Decoded>)) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  match r:
    case Fail{(code, message)}:
      +c = code
      tls_end(conn, tls_cut(some && is_reset(c) && Bool.not(D.close_delimited(s)), s, c, message))
    case Done{xs}:
      match xs:
        case Nil{}:
          tls_end(conn, verdict(D.finish(s)))
        case Con{h, t}:
          +s2 = D.feed(s, h <> t)
          tls_fed(D.done(s2), conn, s2, more)

# Reads until the decoder is done or the stream ends; the fuel argument is
# the same as read_loop's (each productive read finishes the decoder or
# spends at least one byte of budget).
def tls_loop(fuel: Nat, +conn: U32, s: D.State, +some: Bool) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  match fuel:
    case 0n:
      tls_end(conn, verdict(D.finish(s)))
    case 1n+p:
      IO.bind(Result<&1, &1, U32 & String, List<&2, U32>>, Result<&2, &2, M.Error, M.Decoded>,
        T.Tls.recv(conn, 65536),
        r => tls_got(r, conn, s, some, s2 => tls_loop(p, conn, s2, True{})))

def tls_opened(r: Result<&1, &1, U32 & String, U32>, method: M.Method, +max: Nat) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  match r:
    case Fail{(code, message)}:
      fail(tls_error(code, message))
    case Done{conn}:
      tls_loop(2n+max, conn, D.init(method, max), False{})

# One HTTPS exchange with ip:port, verifying the certificate for `host` (the
# name in the URL, also sent as SNI; Tls.open drops one trailing dot for
# both). Tls.open connects, verifies and sends `req`; the response is read
# and decoded as it comes (see above) with a budget of `max` bytes, and the
# connection is closed on every path. Each blocking step is bounded by
# `timeout_ms` inside the foreign code (0: no limit).
def tls(host: String, ip: String, port: Nat, req: List<&2, U32>, method: M.Method, +max: Nat, timeout_ms: Nat) ->
  IO(Result<&2, &2, M.Error, M.Decoded>):
  IO.bind(Result<&1, &1, U32 & String, U32>, Result<&2, &2, M.Error, M.Decoded>,
    T.Tls.open(host, ip, port_u32(port), req, u32(timeout_ms)),
    r => tls_opened(r, method, max))
