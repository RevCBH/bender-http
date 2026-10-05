// DNS
// ===

// getaddrinfo through bun:ffi, the way io_sys reaches libc. JS's IO loop
// cannot park on a lookup (bendlang/bend#1148), so this lane blocks the loop
// until the resolver answers; the C lane runs it on a helper thread instead.
// Codes and order match dns.c: distinct IPv4 addresses, at most 16.
function dns_lookup_lib() {
  if (globalThis.DNS_LOOKUP_LIB === undefined) {
    const ffi = require("bun:ffi");
    const mac = process.platform === "darwin";
    const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
      getaddrinfo: { args: ["ptr", "ptr", "ptr", "ptr"], returns: "i32" },
      freeaddrinfo: { args: ["ptr"], returns: "void" },
      gai_strerror: { args: ["i32"], returns: "cstring" },
    }).symbols;
    // struct addrinfo: ai_addr and ai_canonname swap places on macOS.
    const eai = mac
      ? { again: 2, fail: 4, memory: 6, nodata: 7, noname: 8, system: 11 }
      : { again: -3, fail: -4, memory: -10, nodata: -5, noname: -2, system: -11 };
    globalThis.DNS_LOOKUP_LIB = { ffi, lib, eai, mac, addr_at: mac ? 32 : 24,
      eagain: mac ? 35 : 11 };
  }
  return globalThis.DNS_LOOKUP_LIB;
}

function dns_lookup_fail(code, text) {
  return { $: CID(Fail), error: io_tup(code >>> 0, text) };
}

function dns_lookup(host) {
  if (host.length === 0 || host.includes("\0")) {
    return io_fail(22);
  }
  const { ffi, lib, eai, addr_at, eagain } = dns_lookup_lib();
  const name = new TextEncoder().encode(host + "\0");
  const hints = new Uint8Array(48);
  const view = new DataView(hints.buffer);
  view.setInt32(4, 2, true); // ai_family = AF_INET
  view.setInt32(8, 1, true); // ai_socktype = SOCK_STREAM
  const out = new BigUint64Array(1);
  // As dns.c: a host the resolver reads as an IPv4 address (AI_NUMERICHOST,
  // so inet_aton's octal, hex and short forms) must be the canonical dotted
  // quad, else EINVAL.
  view.setInt32(0, 4, true); // ai_flags = AI_NUMERICHOST
  if (lib.getaddrinfo(ffi.ptr(name), null, ffi.ptr(hints), ffi.ptr(out)) === 0) {
    lib.freeaddrinfo(Number(out[0]));
    if (io_addr(host, 0) === null) {
      return dns_lookup_fail(22, "a numeric host that is not a dotted-quad IPv4 address"
        + " (the resolver would read it as octal, hex or a short form)");
    }
  }
  view.setInt32(0, 0, true);
  out[0] = 0n;
  const rc = lib.getaddrinfo(ffi.ptr(name), null, ffi.ptr(hints), ffi.ptr(out));
  if (rc !== 0) {
    if (rc === eai.system) {
      return io_fail(io_sys().errno() || 5);
    }
    const code = rc === eai.again ? eagain : rc === eai.memory ? 12
      : rc === eai.fail ? 5 : rc === eai.noname || rc === eai.nodata ? 2 : 22;
    return dns_lookup_fail(code, String(lib.gai_strerror(rc)));
  }
  const head = Number(out[0]);
  const found = [];
  for (let ai = head; ai !== 0 && found.length < 16; ai = ffi.read.ptr(ai, 40)) {
    const sa = ffi.read.ptr(ai, addr_at);
    if (ffi.read.i32(ai, 4) !== 2 || sa === 0) {
      continue;
    }
    const ip = [4, 5, 6, 7].map((i) => ffi.read.u8(sa, i)).join(".");
    if (!found.includes(ip)) {
      found.push(ip);
    }
  }
  lib.freeaddrinfo(head);
  if (found.length === 0) {
    return dns_lookup_fail(2, "no IPv4 address for this name");
  }
  let xs = { $: CID(Nil) };
  for (let i = found.length; i > 0; i -= 1) {
    xs = { $: CID(Con), head: found[i - 1], tail: xs };
  }
  return io_done(xs);
}

io_eff(CID(Dns.lookup), dns_lookup);
