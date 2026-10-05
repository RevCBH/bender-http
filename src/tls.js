// TLS
// ===

// The connections tls.c makes (see tls.bend), through bun:ffi: OpenSSL 3
// loaded with dlopen, and the socket calls from libc. As in tls.c, the
// socket is non-blocking: when OpenSSL wants it readable or writable, the
// effect parks on it with io_park_on (the deadline is the step's timeout)
// and the loop resumes it, so a stalled peer does not block other
// computations. Inputs, checks, codes and texts match tls.c, with the
// platform's errno numbers (Linux, else macOS).
function tls_exchange_lib() {
  if (globalThis.TLS_EXCHANGE_LIB !== undefined) {
    return globalThis.TLS_EXCHANGE_LIB;
  }
  const ffi = require("bun:ffi");
  const mac = process.platform === "darwin";
  const sys = io_sys();
  const libc = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
    poll: { args: ["ptr", "u32", "i32"], returns: "i32" },
    [mac ? "__error" : "__errno_location"]: { args: [], returns: "ptr" },
  }).symbols;
  const errno_at = libc[mac ? "__error" : "__errno_location"];
  const E = mac
    ? { inval: 22, fbig: 27, nosys: 78, proto: 100, connaborted: 53, connreset: 54,
      timedout: 60, inprogress: 36, again: 35, intr: 4, nomem: 12, badf: 9, busy: 16 }
    : { inval: 22, fbig: 27, nosys: 38, proto: 71, connaborted: 103, connreset: 104,
      timedout: 110, inprogress: 115, again: 11, intr: 4, nomem: 12, badf: 9, busy: 16 };
  const K = mac
    ? { sol: 0xffff, error: 0x1007, nosigpipe: 0x1022, nonblock: 4 }
    : { sol: 1, error: 4, nosigpipe: 0, nonblock: 0x800 };
  const ssl_syms = {
    TLS_client_method: { args: [], returns: "ptr" },
    SSL_CTX_new: { args: ["ptr"], returns: "ptr" },
    SSL_CTX_free: { args: ["ptr"], returns: "void" },
    SSL_CTX_ctrl: { args: ["ptr", "i32", "i64", "ptr"], returns: "i64" },
    SSL_CTX_set_verify: { args: ["ptr", "i32", "ptr"], returns: "void" },
    SSL_CTX_set_default_verify_paths: { args: ["ptr"], returns: "i32" },
    SSL_CTX_set_alpn_protos: { args: ["ptr", "ptr", "u32"], returns: "i32" },
    SSL_new: { args: ["ptr"], returns: "ptr" },
    SSL_free: { args: ["ptr"], returns: "void" },
    SSL_set_fd: { args: ["ptr", "i32"], returns: "i32" },
    SSL_ctrl: { args: ["ptr", "i32", "i64", "ptr"], returns: "i64" },
    SSL_set1_host: { args: ["ptr", "ptr"], returns: "i32" },
    SSL_set_hostflags: { args: ["ptr", "u32"], returns: "void" },
    SSL_connect: { args: ["ptr"], returns: "i32" },
    SSL_get_error: { args: ["ptr", "i32"], returns: "i32" },
    SSL_get_verify_result: { args: ["ptr"], returns: "i64" },
    SSL_write: { args: ["ptr", "ptr", "i32"], returns: "i32" },
    SSL_read: { args: ["ptr", "ptr", "i32"], returns: "i32" },
    SSL_shutdown: { args: ["ptr"], returns: "i32" },
  };
  const crypto_syms = {
    OpenSSL_version_num: { args: [], returns: "u64" },
    X509_verify_cert_error_string: { args: ["i64"], returns: "cstring" },
    ERR_get_error: { args: [], returns: "u64" },
    ERR_error_string_n: { args: ["u64", "ptr", "u64"], returns: "void" },
    ERR_clear_error: { args: [], returns: "void" },
  };
  const brew = (dir) => [dir + "/libssl.3.dylib", dir + "/libcrypto.3.dylib"];
  const pairs = mac
    ? [["libssl.3.dylib", "libcrypto.3.dylib"], brew("/opt/homebrew/opt/openssl@3/lib"),
      brew("/usr/local/opt/openssl@3/lib"), brew("/opt/local/lib")]
    : [["libssl.so.3", "libcrypto.so.3"], ["libssl.so", "libcrypto.so"]];
  let why = "no library found";
  let ssl = null;
  for (const [ssl_path, crypto_path] of pairs) {
    let c = null;
    let s = null;
    try {
      c = ffi.dlopen(crypto_path, crypto_syms);
      s = ffi.dlopen(ssl_path, ssl_syms);
    } catch (e) {
      why = String(e && e.message ? e.message : e);
      if (c !== null) {
        c.close();
      }
      continue;
    }
    const v = BigInt(c.symbols.OpenSSL_version_num());
    if (v < 0x30000000n) {
      why = ssl_path + " is OpenSSL " + v.toString(16) + ", not 3.x";
      s.close();
      c.close();
      continue;
    }
    ssl = { ...s.symbols, ...c.symbols };
    break;
  }
  globalThis.TLS_EXCHANGE_LIB = { ffi, mac, sys, libc, errno_at, E, K, ssl,
    why: "OpenSSL 3 (libssl) could not be loaded: " + why,
    ctx: null, conns: new Map(), last: 0 };
  return globalThis.TLS_EXCHANGE_LIB;
}

function tls_exchange_fail(code, text) {
  return { $: CID(Fail), error: io_tup(code >>> 0, text) };
}

// A connection's life, as in tls.c.
const TLS_CONNECTING = 0;
const TLS_HANDSHAKING = 1;
const TLS_WRITING = 2;
const TLS_OPEN = 3;
const TLS_ENDED = 4;
const TLS_BROKEN = 5;

const TLS_READ_MAX = 1 << 20;

// A connection for server_name, ip, port and request, every input checked
// (EINVAL) before OpenSSL is loaded (ENOSYS) or a socket is made; or
// { bad: failure }. Its steps answer 0 (done), 1 (wait for x.out ? writable
// : readable, until x.deadline) or -1 (failed: x.code, x.text).
function tls_conn_new(server_name, ip, port, request, timeout_ms) {
  const L = tls_exchange_lib();
  const { ffi, sys, libc, E, K } = L;
  const name = new TextEncoder().encode(server_name + "\0");
  const req = io_unlist(request);
  const addr = ip.includes("\0") || port === 0 ? null : io_addr(ip, port);
  const bad = server_name.length === 0 || server_name.includes("\0")
    ? "the server name is empty or holds a NUL"
    : name.length - 1 > 255 ? "the server name is longer than 255 bytes"
    : addr === null ? "not an IPv4 address and port"
    : req === null ? "a request byte is past 255" : null;
  if (bad !== null) {
    return { bad: tls_exchange_fail(E.inval, bad) };
  }
  if (L.ssl === null) {
    return { bad: tls_exchange_fail(E.nosys, L.why) };
  }
  const S = L.ssl;
  const where = ip + ":" + port;
  // SNI and verification take the name without one trailing dot.
  const host = server_name.length > 1 && server_name.endsWith(".")
    ? server_name.slice(0, -1) : server_name;
  const hostz = new TextEncoder().encode(host + "\0");
  const errno = () => ffi.read.i32(L.errno_at(), 0);
  const clear_errno = () => {
    new Int32Array(ffi.toArrayBuffer(L.errno_at(), 0, 4))[0] = 0;
  };
  const strerror = (code) => String(sys.strerror(code));
  const x = {
    L, S, id: 0, phase: TLS_CONNECTING, fd: -1, ssl: null, busy: false, closing: false,
    name: server_name, where, timeout: timeout_ms, deadline: undefined, out: false,
    req, at: 0, got: 0, code: 0, text: "", chunks: [], len: 0, max: 0,
  };
  const fail = (code, text) => {
    if (x.code === 0) {
      x.code = code;
      x.text = text;
    }
    return -1;
  };
  x.fail = fail;
  // OpenSSL's error queue: the first error (the cause) and its text.
  const err_take = () => {
    const first = BigInt(S.ERR_get_error());
    let text = "no OpenSSL error recorded";
    if (first !== 0n) {
      const buf = new Uint8Array(256);
      S.ERR_error_string_n(first, ffi.ptr(buf), 256n);
      text = new TextDecoder().decode(buf.subarray(0, buf.indexOf(0)));
    }
    while (BigInt(S.ERR_get_error()) !== 0n) {
    }
    return { first, text };
  };
  const err_eof = (e) => (e & 0x80000000n) === 0n && ((e >> 23n) & 0xffn) === 20n
    && (e & 0x7fffffn) === 294n;
  const clock = () => {
    x.deadline = timeout_ms === 0 ? undefined : performance.now() + timeout_ms;
  };
  x.clock = clock;
  const wait = (out, what) => {
    if (x.deadline !== undefined && performance.now() >= x.deadline) {
      return fail(E.timedout, what + " with " + where + " timed out after " + timeout_ms + " ms");
    }
    x.out = out;
    return 1;
  };
  const wants = (kind, code) => kind === 2 || kind === 3 || (kind === 5 && code === E.again);
  x.wants = wants;
  // As tls_step_end: 1 to wait, 2 for a close without close_notify, else -1.
  const step_end = (kind, code, dflt_out, what) => {
    const { first, text } = err_take();
    if (wants(kind, code)) {
      return wait(kind === 3 ? true : kind === 2 ? false : dflt_out, what);
    }
    if (kind === 5 && code !== 0) {
      return fail(code, what + " with " + where + ": " + strerror(code));
    }
    if (kind === 5 || err_eof(first)) {
      return 2;
    }
    if (kind === 6) {
      return fail(E.connreset, what + " with " + where + ": the peer closed the TLS stream");
    }
    return fail(E.connaborted, what + " with " + where + " failed: " + text);
  };
  x.step_end = step_end;
  const sys_fail = (what) => {
    const code = errno();
    return fail(code, what + ": " + strerror(code));
  };
  const connect_start = () => {
    x.fd = sys.socket(2, 1, 0);
    if (x.fd < 0) {
      return sys_fail("socket");
    }
    sys.fcntl(x.fd, 2, 1); // F_SETFD, FD_CLOEXEC
    if (L.mac) {
      sys.setsockopt(x.fd, K.sol, K.nosigpipe, ffi.ptr(new Int32Array([1])), 4);
    }
    const flags = sys.fcntl(x.fd, 3, 0);
    if (flags < 0 || sys.fcntl(x.fd, 4, flags | K.nonblock) !== 0) {
      return sys_fail("fcntl");
    }
    clock();
    if (sys.connect(x.fd, ffi.ptr(addr), 16) === 0) {
      return 0;
    }
    const code = errno();
    if (code !== E.inprogress) {
      return fail(code, "connect to " + where + ": " + strerror(code));
    }
    x.out = true;
    return 1;
  };
  const connect_check = () => {
    const p = new Uint8Array(8);
    const view = new DataView(p.buffer);
    view.setInt32(0, x.fd, true);
    view.setInt16(4, 4, true); // POLLOUT
    const n = libc.poll(ffi.ptr(p), 1, 0);
    if (n < 0 && errno() !== E.intr) {
      const code = errno();
      return fail(code, "connect to " + where + ": " + strerror(code));
    }
    if (n <= 0) {
      if (x.deadline !== undefined && performance.now() >= x.deadline) {
        return fail(E.timedout, "connect to " + where + " timed out after " + timeout_ms + " ms");
      }
      x.out = true;
      return 1;
    }
    const err = new Int32Array(1);
    const len = new Uint32Array([4]);
    const code = sys.getsockopt(x.fd, K.sol, K.error, ffi.ptr(err), ffi.ptr(len)) !== 0
      ? errno() : err[0];
    return code === 0 ? 0 : fail(code, "connect to " + where + ": " + strerror(code));
  };
  // One client context for every connection: TLS 1.2 or later, peer
  // verification against the system's trust store, ALPN http/1.1.
  const ctx = () => {
    if (L.ctx !== null) {
      return L.ctx;
    }
    const c = S.SSL_CTX_new(S.TLS_client_method());
    if (!c) {
      fail(E.nomem, "SSL_CTX_new: " + err_take().text);
      return null;
    }
    const alpn = new Uint8Array([8, ...new TextEncoder().encode("http/1.1")]);
    S.SSL_CTX_set_verify(c, 1, null);
    S.SSL_CTX_ctrl(c, 33, 2, null); // SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER
    if (Number(S.SSL_CTX_ctrl(c, 123, 0x0303, null)) !== 1
      || S.SSL_CTX_set_default_verify_paths(c) !== 1
      || S.SSL_CTX_set_alpn_protos(c, ffi.ptr(alpn), 9) !== 0) {
      fail(E.connaborted, "TLS setup: " + err_take().text);
      S.SSL_CTX_free(c);
      return null;
    }
    L.ctx = c;
    return c;
  };
  // SNI (not for an IPv4 literal) and the name to verify, both without the
  // trailing dot; wildcards only as a whole left-most label.
  const setup = () => {
    const c = ctx();
    if (c === null) {
      return -1;
    }
    x.ssl = S.SSL_new(c);
    const sni = io_addr(host, 443) === null;
    if (!x.ssl || S.SSL_set_fd(x.ssl, x.fd) !== 1
      || (sni && Number(S.SSL_ctrl(x.ssl, 55, 0, ffi.ptr(hostz))) !== 1)
      || S.SSL_set1_host(x.ssl, ffi.ptr(hostz)) !== 1) {
      return fail(E.connaborted, "TLS setup for " + server_name + ": " + err_take().text);
    }
    S.SSL_set_hostflags(x.ssl, 4); // X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS
    return 0;
  };
  const handshake = () => {
    S.ERR_clear_error();
    clear_errno();
    const r = S.SSL_connect(x.ssl);
    const code = errno();
    if (r === 1) {
      return 0;
    }
    const kind = S.SSL_get_error(x.ssl, r);
    const v = BigInt(S.SSL_get_verify_result(x.ssl));
    if (v !== 0n) {
      err_take();
      return fail(E.proto, "certificate verify failed for " + server_name + ": "
        + String(S.X509_verify_cert_error_string(v)));
    }
    const k = step_end(kind, code, false, "TLS handshake");
    return k !== 2 ? k
      : fail(E.connreset, "TLS handshake with " + where + ": the peer closed the connection");
  };
  const write = () => {
    while (x.at < req.length) {
      const part = req.subarray(x.at, x.at + (1 << 30));
      S.ERR_clear_error();
      clear_errno();
      const r = S.SSL_write(x.ssl, ffi.ptr(part), part.length);
      const code = errno();
      if (r <= 0) {
        const k = step_end(S.SSL_get_error(x.ssl, r), code, true, "TLS write");
        return k !== 2 ? k
          : fail(E.connreset, "TLS write to " + where + ": the peer closed the connection");
      }
      x.at += r;
      clock();
    }
    return 0;
  };
  // The open (connect, handshake, write) as far as it can go.
  x.open_step = () => {
    let r = 0;
    if (x.phase === TLS_CONNECTING) {
      r = x.fd < 0 ? connect_start() : connect_check();
      if (r === 0) {
        r = setup();
      }
      if (r === 0) {
        x.phase = TLS_HANDSHAKING;
        clock();
      }
    }
    if (r === 0 && x.phase === TLS_HANDSHAKING) {
      r = handshake();
      if (r === 0) {
        x.phase = TLS_WRITING;
        clock();
      }
    }
    if (r === 0 && x.phase === TLS_WRITING) {
      r = write();
      if (r === 0) {
        x.phase = TLS_OPEN;
      }
    }
    if (r < 0) {
      x.phase = TLS_BROKEN;
    }
    return r;
  };
  // One SSL_read of at most n bytes: the count (> 0, gathered in x.chunks),
  // 0 at the peer's close_notify (ended), or -kind with x.sys set.
  const buf = new Uint8Array(16384);
  x.read_once = (n) => {
    S.ERR_clear_error();
    clear_errno();
    const r = S.SSL_read(x.ssl, ffi.ptr(buf), Math.min(buf.length, n));
    x.sys = errno();
    if (r > 0) {
      x.chunks.push(buf.slice(0, r));
      x.len += r;
      x.got += r;
      return r;
    }
    const kind = S.SSL_get_error(x.ssl, r);
    if (kind === 6) {
      S.ERR_clear_error();
      S.SSL_shutdown(x.ssl);
      S.ERR_clear_error();
      x.phase = TLS_ENDED;
      return 0;
    }
    return -kind;
  };
  // The bytes gathered so far, as a List; the gathering starts over.
  x.take = () => {
    const out = new Uint8Array(x.len);
    let at = 0;
    for (const c of x.chunks) {
      out.set(c, at);
      at += c.length;
    }
    x.chunks = [];
    x.len = 0;
    return io_list(out, out.length);
  };
  x.free = () => {
    if (x.ssl) {
      if (x.phase === TLS_OPEN) {
        S.ERR_clear_error();
        S.SSL_shutdown(x.ssl); // close_notify, if the socket takes it
      }
      S.SSL_free(x.ssl);
      x.ssl = null;
    }
    if (x.fd >= 0) {
      sys.close(x.fd);
      x.fd = -1;
    }
    S.ERR_clear_error();
  };
  return { conn: x };
}

// Parks x's step on its socket until it is ready or the deadline passes.
function tls_park(x, k, more) {
  io_park_on(x.fd, x.out, k, more, x.deadline);
  return undefined;
}

// Tls.exchange: the open, then everything until the peer closes, at most
// max bytes (one more is EFBIG). A close without close_notify after some
// data ends it too.
function tls_exchange(server_name, ip, port, request, max, timeout_ms, k) {
  const made = tls_conn_new(server_name, ip, port, request, timeout_ms);
  if (made.bad !== undefined) {
    return made.bad;
  }
  const x = made.conn;
  const { E } = x.L;
  const drain = () => {
    for (;;) {
      if (x.len > max) {
        x.fail(E.fbig, "the response from " + x.where + " is longer than " + max + " bytes");
        x.phase = TLS_BROKEN;
        return 0;
      }
      const r = x.read_once(max + 1 - x.len);
      if (r > 0) {
        x.clock();
        continue;
      }
      if (r === 0) {
        return 0;
      }
      const s = x.step_end(-r, x.sys, false, "TLS read");
      if (s === 1) {
        return 1;
      }
      if (s === 2 && x.len > 0) {
        x.phase = TLS_ENDED;
        return 0;
      }
      if (s === 2) {
        x.fail(E.connreset, "TLS read from " + x.where
          + ": the peer closed the connection before any response");
      }
      x.phase = TLS_BROKEN;
      return 0;
    }
  };
  const more = () => {
    let r = x.phase < TLS_OPEN ? x.open_step() : 0;
    if (r === 0) {
      r = drain();
    }
    if (r === 1) {
      return tls_park(x, k, more);
    }
    const t = x.phase === TLS_ENDED ? io_done(x.take()) : tls_exchange_fail(x.code, x.text);
    x.free();
    return t;
  };
  return more();
}

// Tls.open: the open; the connection goes into the table under a handle.
function tls_open(server_name, ip, port, request, timeout_ms, k) {
  const made = tls_conn_new(server_name, ip, port, request, timeout_ms);
  if (made.bad !== undefined) {
    return made.bad;
  }
  const x = made.conn;
  const L = x.L;
  const more = () => {
    const r = x.open_step();
    if (r === 1) {
      return tls_park(x, k, more);
    }
    if (r < 0) {
      const t = tls_exchange_fail(x.code, x.text);
      x.free();
      return t;
    }
    L.last = L.last === 0xffffffff ? 1 : L.last + 1;
    x.id = L.last;
    L.conns.set(x.id, x);
    return io_done(x.id);
  };
  return more();
}

// Tls.recv: up to max bytes, as soon as there are some; [] once the peer
// closed with close_notify. A failure or close right after some bytes waits
// for the next call (the bytes go first).
function tls_recv(conn, max, k) {
  const L = tls_exchange_lib();
  const { E } = L;
  const x = L.conns.get(conn);
  if (x === undefined) {
    return tls_exchange_fail(E.badf, "no open TLS connection has this handle");
  }
  if (x.busy) {
    return tls_exchange_fail(E.busy, "another Tls.recv is waiting on this connection");
  }
  if (max === 0) {
    return tls_exchange_fail(E.inval, "a read of 0 bytes");
  }
  if (x.phase === TLS_ENDED) {
    return io_done({ $: CID(Nil) });
  }
  if (x.phase === TLS_BROKEN) {
    return tls_exchange_fail(x.code, x.text);
  }
  const n = Math.min(max, TLS_READ_MAX);
  const step = () => {
    while (x.len < n) {
      const r = x.read_once(n - x.len);
      if (r > 0) {
        continue;
      }
      if (r === 0) {
        return 0;
      }
      if (x.wants(-r, x.sys) && x.len > 0) {
        x.S.ERR_clear_error();
        return 0;
      }
      const s = x.step_end(-r, x.sys, false, "TLS read");
      if (s === 1) {
        return 1;
      }
      if (s === 2) {
        x.fail(E.connreset, "TLS read from " + x.where + (x.got > 0
          ? ": the peer closed the connection without close_notify"
          : ": the peer closed the connection before any response"));
      }
      x.phase = TLS_BROKEN;
      return 0;
    }
    return 0;
  };
  const more = () => {
    if (step() === 1) {
      return tls_park(x, k, more);
    }
    const t = x.len > 0 ? io_done(x.take())
      : x.phase === TLS_ENDED ? io_done({ $: CID(Nil) })
      : tls_exchange_fail(x.code, x.text);
    x.busy = false;
    if (x.closing) {
      x.free();
    }
    return t;
  };
  x.busy = true;
  x.chunks = [];
  x.len = 0;
  x.clock();
  return more();
}

// Tls.close: an unknown handle is a no-op; a connection a Tls.recv is
// parked on leaves the table now and is freed when that read ends.
function tls_close(conn) {
  const L = tls_exchange_lib();
  const x = L.conns.get(conn);
  if (x !== undefined) {
    L.conns.delete(conn);
    if (x.busy) {
      x.closing = true;
    } else {
      x.free();
    }
  }
  return { $: CID(Unit) };
}

io_eff(CID(Tls.exchange), tls_exchange);
io_eff(CID(Tls.open), tls_open);
io_eff(CID(Tls.recv), tls_recv);
io_eff(CID(Tls.close), tls_close);
