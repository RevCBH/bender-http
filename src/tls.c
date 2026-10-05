// TLS
// ===

#include <dlfcn.h>
#include <stdarg.h>

// HTTPS connections over OpenSSL 3 (see tls.bend): connect, TLS 1.2+
// handshake with SNI and certificate + host name verification, write the
// request, then read. OpenSSL 3 is loaded with dlopen the first time an
// effect runs, so no program needs a linker flag.
//
// Everything runs on the loop thread with a non-blocking socket: when
// OpenSSL wants the socket readable or writable, the effect parks on it with
// io_wait_on (the deadline is the step's timeout), as Base's TCP effects do,
// and the loop resumes it. No IO helper thread is held, so stalled peers
// cannot starve the runtime's helpers (Dns.lookup, files, processes).
//
// Tls.exchange runs one connection to the end and frees it. Tls.open leaves
// it in a table of open connections under a U32 handle (Base's handle types
// are closed); Tls.recv reads from it and Tls.close frees it.

// OpenSSL's headers are not included (they may be absent); these are the
// values behind the macros the code uses, stable across OpenSSL 3.x.
#define TLS_CTRL_MODE          33      // SSL_CTX_set_mode
#define TLS_MODE_MOVING_BUFFER 0x2     // SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER
#define TLS_CTRL_SET_MIN_PROTO 123     // SSL_CTX_set_min_proto_version
#define TLS_VERSION_1_2        0x0303
#define TLS_CTRL_SET_HOSTNAME  55      // SSL_set_tlsext_host_name
#define TLS_NAMETYPE_HOST      0
#define TLS_VERIFY_PEER        1
#define TLS_NO_PARTIAL_WILD    0x4     // X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS
#define TLS_ERROR_WANT_READ    2
#define TLS_ERROR_WANT_WRITE   3
#define TLS_ERROR_SYSCALL      5
#define TLS_ERROR_ZERO_RETURN  6
#define TLS_ERR_LIB_SSL        20
#define TLS_R_UNEXPECTED_EOF   294     // SSL_R_UNEXPECTED_EOF_WHILE_READING
#define TLS_CHUNK              16384
#define TLS_READ_MAX           (1u << 20)  // the most one Tls.recv answers
#define TLS_NAME_MAX           255     // the SNI limit

typedef struct {
  const void*   (*TLS_client_method)(void);
  void*         (*SSL_CTX_new)(const void*);
  void          (*SSL_CTX_free)(void*);
  long          (*SSL_CTX_ctrl)(void*, int, long, void*);
  void          (*SSL_CTX_set_verify)(void*, int, void*);
  int           (*SSL_CTX_set_default_verify_paths)(void*);
  int           (*SSL_CTX_set_alpn_protos)(void*, const unsigned char*, unsigned);
  void*         (*SSL_new)(void*);
  void          (*SSL_free)(void*);
  int           (*SSL_set_fd)(void*, int);
  long          (*SSL_ctrl)(void*, int, long, void*);
  int           (*SSL_set1_host)(void*, const char*);
  void          (*SSL_set_hostflags)(void*, unsigned);
  int           (*SSL_connect)(void*);
  int           (*SSL_get_error)(const void*, int);
  long          (*SSL_get_verify_result)(const void*);
  int           (*SSL_write)(void*, const void*, int);
  int           (*SSL_read)(void*, void*, int);
  int           (*SSL_shutdown)(void*);
  unsigned long (*OpenSSL_version_num)(void);
  const char*   (*X509_verify_cert_error_string)(long);
  unsigned long (*ERR_get_error)(void);
  void          (*ERR_error_string_n)(unsigned long, char*, size_t);
  void          (*ERR_clear_error)(void);
} TlsLib;

// The library is loaded once, by the loop thread; state 1 is loaded, -1 is
// failed for good (tls_lib_why says why).
static TlsLib tls_lib;
static int    tls_lib_state;
static char   tls_lib_why[512];

static const char* const tls_lib_paths[][2] = {
#ifdef __APPLE__
  { "libssl.3.dylib", "libcrypto.3.dylib" },
  { "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib",
    "/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib" },
  { "/usr/local/opt/openssl@3/lib/libssl.3.dylib",
    "/usr/local/opt/openssl@3/lib/libcrypto.3.dylib" },
  { "/opt/local/lib/libssl.3.dylib", "/opt/local/lib/libcrypto.3.dylib" },
#else
  { "libssl.so.3", "libcrypto.so.3" },
  { "libssl.so", "libcrypto.so" },
#endif
};

#define TLS_SYM(lib, name) \
  ((t->name = (__typeof__(t->name))dlsym(lib, #name)) != NULL)

// Loads one libssl/libcrypto pair into t: 0 when every symbol is there and
// the library is OpenSSL 3 or later, else -1 (both handles closed).
static int tls_lib_try(TlsLib* t, const char* ssl_path, const char* crypto_path) {
  void* crypto = dlopen(crypto_path, RTLD_NOW | RTLD_LOCAL);
  void* ssl    = crypto != NULL ? dlopen(ssl_path, RTLD_NOW | RTLD_LOCAL) : NULL;
  if (ssl == NULL) {
    const char* why = dlerror();
    snprintf(tls_lib_why, sizeof tls_lib_why, "%s", why != NULL ? why : ssl_path);
    if (crypto != NULL) {
      dlclose(crypto);
    }
    return -1;
  }
  int ok = TLS_SYM(ssl, TLS_client_method) && TLS_SYM(ssl, SSL_CTX_new)
    && TLS_SYM(ssl, SSL_CTX_free) && TLS_SYM(ssl, SSL_CTX_ctrl)
    && TLS_SYM(ssl, SSL_CTX_set_verify)
    && TLS_SYM(ssl, SSL_CTX_set_default_verify_paths)
    && TLS_SYM(ssl, SSL_CTX_set_alpn_protos) && TLS_SYM(ssl, SSL_new)
    && TLS_SYM(ssl, SSL_free) && TLS_SYM(ssl, SSL_set_fd)
    && TLS_SYM(ssl, SSL_ctrl) && TLS_SYM(ssl, SSL_set1_host)
    && TLS_SYM(ssl, SSL_set_hostflags)
    && TLS_SYM(ssl, SSL_connect) && TLS_SYM(ssl, SSL_get_error)
    && TLS_SYM(ssl, SSL_get_verify_result) && TLS_SYM(ssl, SSL_write)
    && TLS_SYM(ssl, SSL_read) && TLS_SYM(ssl, SSL_shutdown)
    && TLS_SYM(crypto, OpenSSL_version_num)
    && TLS_SYM(crypto, X509_verify_cert_error_string)
    && TLS_SYM(crypto, ERR_get_error) && TLS_SYM(crypto, ERR_error_string_n)
    && TLS_SYM(crypto, ERR_clear_error);
  if (!ok) {
    snprintf(tls_lib_why, sizeof tls_lib_why, "%s lacks an OpenSSL 3 symbol", ssl_path);
  } else if (t->OpenSSL_version_num() < 0x30000000UL) {
    snprintf(tls_lib_why, sizeof tls_lib_why, "%s is OpenSSL %lx, not 3.x",
      ssl_path, t->OpenSSL_version_num());
    ok = 0;
  }
  if (!ok) {
    dlclose(ssl);
    dlclose(crypto);
    return -1;
  }
  return 0;
}

static const TlsLib* tls_lib_load(void) {
  for (u32 i = 0; tls_lib_state == 0 && i < sizeof tls_lib_paths / sizeof tls_lib_paths[0]; i += 1) {
    tls_lib_state = tls_lib_try(&tls_lib, tls_lib_paths[i][0], tls_lib_paths[i][1]) == 0 ? 1 : 0;
  }
  if (tls_lib_state == 0) {
    char why[sizeof tls_lib_why];
    memcpy(why, tls_lib_why, sizeof why);
    snprintf(tls_lib_why, sizeof tls_lib_why,
      "OpenSSL 3 (libssl) could not be loaded: %s", why);
    tls_lib_state = -1;
  }
  return tls_lib_state == 1 ? &tls_lib : NULL;
}

// A connection's life: the open's three steps, then open (requests read
// from it), then over: ended (the peer's close_notify) or broken (code and
// text say why; every later read answers that again).
enum { TLS_CONNECTING, TLS_HANDSHAKING, TLS_WRITING, TLS_OPEN, TLS_ENDED, TLS_BROKEN };

typedef struct TlsConn {
  const TlsLib*      lib;
  u32                id;        // the handle, once in the open table
  int                phase;
  int                fd;
  void*              ssl;
  int                busy;      // an effect is parked on it
  int                closing;   // Tls.close came while busy: free when it ends
  char*              name;      // the server name as given (for messages)
  char*              host;      // without one trailing dot: SNI and verification
  char*              req;
  u64                req_len;
  u64                req_at;
  struct sockaddr_in addr;
  char               where[INET_ADDRSTRLEN + 8];
  u32                timeout;   // ms, 0: none
  u64                deadline;  // io_tick() units, 0: none
  short              want;      // POLLIN or POLLOUT, while parked
  u64                got;       // bytes read over the connection's life
  u32                code;
  char               text[640];
  char*              out;       // what the current read effect gathers
  u64                len;
  u64                cap;
  u64                max;
  struct TlsConn*    next;      // the open table
} TlsConn;

// Records the failure (the first one wins) and answers -1.
static int tls_fail(TlsConn* x, u32 code, const char* fmt, ...) {
  if (x->code == 0) {
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(x->text, sizeof x->text, fmt, ap);
    va_end(ap);
    x->code = code;
  }
  return -1;
}

// Takes OpenSSL's error queue: the first error, which is the cause, as text
// in buf; the code answered is that first error, or 0.
static unsigned long tls_err_take(const TlsLib* l, char* buf, size_t n) {
  unsigned long first = l->ERR_get_error();
  unsigned long more  = first;
  snprintf(buf, n, "no OpenSSL error recorded");
  if (first != 0) {
    l->ERR_error_string_n(first, buf, n);
  }
  while (more != 0) {
    more = l->ERR_get_error();
  }
  return first;
}

// OpenSSL 3's report of a close without close_notify.
static int tls_err_eof(unsigned long e) {
  return (e & 0x80000000UL) == 0 && ((e >> 23) & 0xFF) == TLS_ERR_LIB_SSL
    && (e & 0x7FFFFF) == TLS_R_UNEXPECTED_EOF;
}

// Starts the current step's clock: its deadline is timeout_ms from now.
static void tls_clock(TlsConn* x) {
  x->deadline = x->timeout == 0 ? 0 : io_tick() + (u64)x->timeout * 1000000ull;
}

// The step must wait for the socket (evts): 1, or a timeout (-1) once the
// step's deadline has passed.
static int tls_wait(TlsConn* x, short evts, const char* what) {
  if (x->deadline != 0 && io_tick() >= x->deadline) {
    return tls_fail(x, ETIMEDOUT, "%s with %s timed out after %u ms", what, x->where, x->timeout);
  }
  x->want = evts;
  return 1;
}

static int tls_wants(int kind, int sys) {
  return kind == TLS_ERROR_WANT_READ || kind == TLS_ERROR_WANT_WRITE
    || (kind == TLS_ERROR_SYSCALL && (sys == EAGAIN || sys == EWOULDBLOCK));
}

// What an I/O step's outcome means: kind is SSL_get_error's answer, sys the
// errno right after the call. Answers 1 to wait for the socket, 2 when the
// peer closed the stream without close_notify (the caller decides), else
// records the failure and answers -1.
static int tls_step_end(TlsConn* x, int kind, int sys, short dflt, const char* what) {
  char          why[256];
  unsigned long e = tls_err_take(x->lib, why, sizeof why);
  if (tls_wants(kind, sys)) {
    return tls_wait(x, kind == TLS_ERROR_WANT_READ ? POLLIN
      : kind == TLS_ERROR_WANT_WRITE ? POLLOUT : dflt, what);
  }
  if (kind == TLS_ERROR_SYSCALL && sys != 0) {
    return tls_fail(x, (u32)sys, "%s with %s: %s", what, x->where, strerror(sys));
  }
  if (kind == TLS_ERROR_SYSCALL || tls_err_eof(e)) {
    return 2;
  }
  if (kind == TLS_ERROR_ZERO_RETURN) {
    return tls_fail(x, ECONNRESET, "%s with %s: the peer closed the TLS stream", what, x->where);
  }
  return tls_fail(x, ECONNABORTED, "%s with %s failed: %s", what, x->where, why);
}

static int tls_sys_fail(TlsConn* x, const char* what) {
  int sys = errno;
  return tls_fail(x, (u32)sys, "%s: %s", what, strerror(sys));
}

// A non-blocking socket connecting to x->addr: 0 connected, 1 to wait.
static int tls_connect_start(TlsConn* x) {
  x->fd = socket(AF_INET, SOCK_STREAM, 0);
  if (x->fd < 0) {
    return tls_sys_fail(x, "socket");
  }
  fcntl(x->fd, F_SETFD, FD_CLOEXEC);
#ifdef SO_NOSIGPIPE
  int one = 1;
  setsockopt(x->fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
#endif
  int flags = fcntl(x->fd, F_GETFL, 0);
  if (flags < 0 || fcntl(x->fd, F_SETFL, flags | O_NONBLOCK) != 0) {
    return tls_sys_fail(x, "fcntl");
  }
  tls_clock(x);
  if (connect(x->fd, (struct sockaddr*)&x->addr, sizeof x->addr) == 0) {
    return 0;
  }
  if (errno != EINPROGRESS) {
    int sys = errno;
    return tls_fail(x, (u32)sys, "connect to %s: %s", x->where, strerror(sys));
  }
  x->want = POLLOUT;
  return 1;
}

// After a wait on a connecting socket: 0 connected, 1 to wait again.
static int tls_connect_check(TlsConn* x) {
  struct pollfd p = { x->fd, POLLOUT, 0 };
  int           n = poll(&p, 1, 0);
  if (n < 0 && errno != EINTR) {
    int sys = errno;
    return tls_fail(x, (u32)sys, "connect to %s: %s", x->where, strerror(sys));
  }
  if (n <= 0) {
    if (x->deadline != 0 && io_tick() >= x->deadline) {
      return tls_fail(x, ETIMEDOUT, "connect to %s timed out after %u ms", x->where, x->timeout);
    }
    x->want = POLLOUT;
    return 1;
  }
  int       err = 0;
  socklen_t len = sizeof err;
  if (getsockopt(x->fd, SOL_SOCKET, SO_ERROR, &err, &len) != 0) {
    err = errno;
  }
  return err == 0 ? 0
    : tls_fail(x, (u32)err, "connect to %s: %s", x->where, strerror(err));
}

// One client context for every connection (made on the loop thread, which
// is the only one that uses it): TLS 1.2 or later, peer verification against
// the system's trust store, ALPN http/1.1.
static void* tls_ctx_shared;

static void* tls_ctx(TlsConn* x) {
  const TlsLib* l   = x->lib;
  char          why[256];
  if (tls_ctx_shared != NULL) {
    return tls_ctx_shared;
  }
  void* ctx = l->SSL_CTX_new(l->TLS_client_method());
  if (ctx == NULL) {
    tls_err_take(l, why, sizeof why);
    tls_fail(x, ENOMEM, "SSL_CTX_new: %s", why);
    return NULL;
  }
  l->SSL_CTX_set_verify(ctx, TLS_VERIFY_PEER, NULL);
  l->SSL_CTX_ctrl(ctx, TLS_CTRL_MODE, TLS_MODE_MOVING_BUFFER, NULL);
  if (l->SSL_CTX_ctrl(ctx, TLS_CTRL_SET_MIN_PROTO, TLS_VERSION_1_2, NULL) != 1
    || l->SSL_CTX_set_default_verify_paths(ctx) != 1
    || l->SSL_CTX_set_alpn_protos(ctx, (const unsigned char*)"\x08http/1.1", 9) != 0) {
    tls_err_take(l, why, sizeof why);
    tls_fail(x, ECONNABORTED, "TLS setup: %s", why);
    l->SSL_CTX_free(ctx);
    return NULL;
  }
  tls_ctx_shared = ctx;
  return ctx;
}

// The connection object on the connected socket: SNI (unless the host is an
// IPv4 literal, which SNI forbids) and the name the certificate must match,
// both without the name's trailing dot (RFC 6066 §3; certificates hold no
// trailing dots). The match takes DNS SANs (and IP SANs for a literal); a
// wildcard must be a whole left-most label (RFC 9525 §6.3).
static int tls_setup(TlsConn* x) {
  const TlsLib*  l   = x->lib;
  void*          ctx = tls_ctx(x);
  char           why[256];
  struct in_addr literal;
  if (ctx == NULL) {
    return -1;
  }
  x->ssl  = l->SSL_new(ctx);
  int sni = inet_pton(AF_INET, x->host, &literal) != 1;
  if (x->ssl == NULL || l->SSL_set_fd(x->ssl, x->fd) != 1
    || (sni && l->SSL_ctrl(x->ssl, TLS_CTRL_SET_HOSTNAME, TLS_NAMETYPE_HOST, x->host) != 1)
    || l->SSL_set1_host(x->ssl, x->host) != 1) {
    tls_err_take(l, why, sizeof why);
    return tls_fail(x, ECONNABORTED, "TLS setup for %s: %s", x->name, why);
  }
  l->SSL_set_hostflags(x->ssl, TLS_NO_PARTIAL_WILD);
  return 0;
}

static int tls_handshake(TlsConn* x) {
  const TlsLib* l = x->lib;
  l->ERR_clear_error();
  errno    = 0;
  int r    = l->SSL_connect(x->ssl);
  int sys  = errno;
  if (r == 1) {
    return 0;
  }
  int  kind = l->SSL_get_error(x->ssl, r);
  long v    = l->SSL_get_verify_result(x->ssl);
  if (v != 0) {
    char why[256];
    tls_err_take(l, why, sizeof why);
    return tls_fail(x, EPROTO, "certificate verify failed for %s: %s",
      x->name, l->X509_verify_cert_error_string(v));
  }
  int k = tls_step_end(x, kind, sys, POLLIN, "TLS handshake");
  return k != 2 ? k
    : tls_fail(x, ECONNRESET, "TLS handshake with %s: the peer closed the connection", x->where);
}

// Writes what is left of the request; each piece written restarts the clock.
static int tls_write(TlsConn* x) {
  const TlsLib* l = x->lib;
  while (x->req_at < x->req_len) {
    u64 left = x->req_len - x->req_at;
    int part = left < (1u << 30) ? (int)left : (1 << 30);
    l->ERR_clear_error();
    errno   = 0;
    int r   = l->SSL_write(x->ssl, x->req + x->req_at, part);
    int sys = errno;
    if (r <= 0) {
      int k = tls_step_end(x, l->SSL_get_error(x->ssl, r), sys, POLLOUT, "TLS write");
      return k != 2 ? k
        : tls_fail(x, ECONNRESET, "TLS write to %s: the peer closed the connection", x->where);
    }
    x->req_at += (u64)r;
    tls_clock(x);
  }
  return 0;
}

// Runs the open (connect, handshake, write) as far as it can go: 0 once the
// connection is open, 1 to wait for x->want, -1 on failure (broken).
static int tls_open_step(TlsConn* x) {
  int r = 0;
  if (x->phase == TLS_CONNECTING) {
    r = x->fd < 0 ? tls_connect_start(x) : tls_connect_check(x);
    if (r == 0) {
      r = tls_setup(x);
    }
    if (r == 0) {
      x->phase = TLS_HANDSHAKING;
      tls_clock(x);
    }
  }
  if (r == 0 && x->phase == TLS_HANDSHAKING) {
    r = tls_handshake(x);
    if (r == 0) {
      x->phase = TLS_WRITING;
      tls_clock(x);
    }
  }
  if (r == 0 && x->phase == TLS_WRITING) {
    r = tls_write(x);
    if (r == 0) {
      x->phase = TLS_OPEN;
    }
  }
  if (r < 0) {
    x->phase = TLS_BROKEN;
  }
  return r;
}

// One SSL_read into x->out past x->len, at most n bytes: the count (> 0), 0
// at the peer's close_notify (ended), or the kind of failure as -kind with
// *sys set.
static int tls_read_once(TlsConn* x, u64 n, int* sys) {
  const TlsLib* l    = x->lib;
  int           want = n < (1u << 30) ? (int)n : (1 << 30);
  l->ERR_clear_error();
  errno  = 0;
  int r  = l->SSL_read(x->ssl, x->out + x->len, want);
  *sys   = errno;
  if (r > 0) {
    x->len += (u64)r;
    x->got += (u64)r;
    return r;
  }
  int kind = l->SSL_get_error(x->ssl, r);
  if (kind == TLS_ERROR_ZERO_RETURN) {
    l->ERR_clear_error();
    l->SSL_shutdown(x->ssl);
    l->ERR_clear_error();
    x->phase = TLS_ENDED;
    return 0;
  }
  return -kind;
}

static void tls_conn_free(TlsConn* x) {
  if (x->ssl != NULL) {
    if (x->phase == TLS_OPEN) {
      x->lib->ERR_clear_error();
      x->lib->SSL_shutdown(x->ssl);   // close_notify, if the socket takes it
    }
    x->lib->SSL_free(x->ssl);
  }
  if (x->fd >= 0) {
    close(x->fd);
  }
  if (x->lib != NULL) {
    x->lib->ERR_clear_error();
  }
  free(x->name);
  free(x->host);
  free(x->req);
  free(x->out);
  free(x);
}

// A connection for f's server_name (f[0]), ip (f[1]), port (f[2]) and
// request (f[3]), every input checked (EINVAL) before OpenSSL is loaded
// (ENOSYS) or a socket is made. NULL when one fails, with *code and *why.
static TlsConn* tls_conn_new(Env e, Term* f, u32 timeout, u32* code, const char** why) {
  TlsConn* x        = (TlsConn*)io_mem(calloc(1, sizeof(TlsConn)));
  u64      ip_len   = 0;
  u64      name_len = 0;
  x->fd             = -1;
  x->timeout        = timeout;
  x->name           = io_cstr(e, f[0], &name_len);
  char*    ip       = io_cstr(e, f[1], &ip_len);
  u32      port     = (u32)f[2];
  x->req            = io_cbuf(e, f[3], &x->req_len, CID(Con));
  const char* bad   = name_len == 0 || io_nul(x->name, name_len)
    ? "the server name is empty or holds a NUL"
    : name_len > TLS_NAME_MAX ? "the server name is longer than 255 bytes"
    : io_nul(ip, ip_len) || port == 0 || io_sys_addr(ip, port, &x->addr) != 0
    ? "not an IPv4 address and port" : x->req == NULL ? "a request byte is past 255"
    : NULL;
  snprintf(x->where, sizeof x->where, "%s:%u", bad == NULL ? ip : "?", port);
  free(ip);
  x->host         = io_mem(strdup(x->name));
  size_t host_len = strlen(x->host);   // shorter than name_len past a NUL
  if (host_len > 1 && x->host[host_len - 1] == '.') {
    x->host[host_len - 1] = 0;
  }
  *code = EINVAL;
  *why  = bad;
  if (bad == NULL && (x->lib = tls_lib_load()) == NULL) {
    *code = ENOSYS;
    *why  = tls_lib_why;
  }
  if (*why != NULL) {
    tls_conn_free(x);
    return NULL;
  }
  return x;
}

// Tls.exchange
// ------------

#ifdef CID(Tls.exchange)

// Reads until the peer closes: 0 once over (ended or broken), 1 to wait.
// At most max bytes (one more is EFBIG); the buffer grows by doubling, never
// past max + 1. A close without close_notify after some data ends it too.
static int tls_drain_step(TlsConn* x) {
  u64 limit = x->max + 1;
  for (;;) {
    if (x->len >= limit) {
      tls_fail(x, EFBIG, "the response from %s is longer than %llu bytes",
        x->where, (unsigned long long)x->max);
      x->phase = TLS_BROKEN;
      return 0;
    }
    if (x->len == x->cap) {
      u64   cap = x->cap * 2 < TLS_CHUNK ? TLS_CHUNK : x->cap * 2;
      cap       = cap < limit ? cap : limit;
      char* out = realloc(x->out, cap);
      if (out == NULL) {
        tls_fail(x, ENOMEM, "no memory for the response");
        x->phase = TLS_BROKEN;
        return 0;
      }
      x->out = out;
      x->cap = cap;
    }
    int sys = 0;
    int r   = tls_read_once(x, x->cap - x->len, &sys);
    if (r > 0) {
      tls_clock(x);
      continue;
    }
    if (r == 0) {
      return 0;
    }
    int k = tls_step_end(x, -r, sys, POLLIN, "TLS read");
    if (k == 1) {
      return 1;
    }
    if (k == 2 && x->len > 0) {
      x->phase = TLS_ENDED;
      return 0;
    }
    if (k == 2) {
      tls_fail(x, ECONNRESET,
        "TLS read from %s: the peer closed the connection before any response", x->where);
    }
    x->phase = TLS_BROKEN;
    return 0;
  }
}

static Term tls_exchange_more(Env e, IoWork* w) {
  TlsConn* x = (TlsConn*)w->data;
  int      r = x->phase < TLS_OPEN ? tls_open_step(x) : 0;
  if (r == 0) {
    r = tls_drain_step(x);
  }
  if (r == 1) {
    return io_wait_on(w, x->fd, x->want, x->deadline, tls_exchange_more);
  }
  Term t = x->phase == TLS_ENDED ? io_done(e, io_list(e, x->out, x->len))
    : io_fail(e, x->code, x->text);
  tls_conn_free(x);
  return t;
}

// f: server_name, ip, port, request, max, timeout_ms.
Term tls_exchange_run(Env e, Term* f, IoWork* w) {
  u32         code = 0;
  const char* why  = NULL;
  TlsConn*    x    = tls_conn_new(e, f, (u32)f[5], &code, &why);
  if (x == NULL) {
    return io_fail(e, code, why);
  }
  x->max  = (u32)f[4];
  w->data = (char*)x;
  return tls_exchange_more(e, w);
}

static void __attribute__((constructor)) tls_exchange_use(void) {
  io_eff(CID(Tls.exchange), tls_exchange_run, 0);
}

#endif

// The open table: Tls.open's connections by handle (never 0, never reused
// in practice: 2^32 handles). Only the loop thread touches it.
static TlsConn* tls_conns;
static u32      tls_conns_last;

static __attribute__((unused)) TlsConn* tls_conns_find(u32 id) {
  TlsConn* x = tls_conns;
  while (x != NULL && x->id != id) {
    x = x->next;
  }
  return x;
}

static __attribute__((unused)) void tls_conns_add(TlsConn* x) {
  tls_conns_last += tls_conns_last == 0xFFFFFFFFu ? 2 : 1;
  x->id     = tls_conns_last;
  x->next   = tls_conns;
  tls_conns = x;
}

static __attribute__((unused)) void tls_conns_drop(TlsConn* x) {
  TlsConn** at = &tls_conns;
  while (*at != NULL && *at != x) {
    at = &(*at)->next;
  }
  if (*at == x) {
    *at = x->next;
  }
}

// Tls.open
// --------

#ifdef CID(Tls.open)

static Term tls_open_more(Env e, IoWork* w) {
  TlsConn* x = (TlsConn*)w->data;
  int      r = tls_open_step(x);
  if (r == 1) {
    return io_wait_on(w, x->fd, x->want, x->deadline, tls_open_more);
  }
  if (r < 0) {
    Term t = io_fail(e, x->code, x->text);
    tls_conn_free(x);
    return t;
  }
  tls_conns_add(x);
  return io_done(e, (Term)x->id);
}

// f: server_name, ip, port, request, timeout_ms.
Term tls_open_run(Env e, Term* f, IoWork* w) {
  u32         code = 0;
  const char* why  = NULL;
  TlsConn*    x    = tls_conn_new(e, f, (u32)f[4], &code, &why);
  if (x == NULL) {
    return io_fail(e, code, why);
  }
  w->data = (char*)x;
  return tls_open_more(e, w);
}

static void __attribute__((constructor)) tls_open_use(void) {
  io_eff(CID(Tls.open), tls_open_run, 0);
}

#endif

// Tls.recv
// --------

#ifdef CID(Tls.recv)

// One Tls.recv: up to x->max bytes, as soon as there are some. Answers 1 to
// wait; 0 when the answer is ready: x->len bytes, or none when the
// connection is over. A failure or close right after some bytes waits for
// the next call (the bytes go first).
static int tls_recv_step(TlsConn* x) {
  while (x->len < x->max) {
    int sys = 0;
    int r   = tls_read_once(x, x->max - x->len, &sys);
    if (r > 0) {
      continue;
    }
    if (r == 0) {
      return 0;
    }
    if (tls_wants(-r, sys) && x->len > 0) {
      x->lib->ERR_clear_error();
      return 0;
    }
    int k = tls_step_end(x, -r, sys, POLLIN, "TLS read");
    if (k == 1) {
      return 1;
    }
    if (k == 2) {
      tls_fail(x, ECONNRESET, x->got > 0
        ? "TLS read from %s: the peer closed the connection without close_notify"
        : "TLS read from %s: the peer closed the connection before any response", x->where);
    }
    x->phase = TLS_BROKEN;
    return 0;
  }
  return 0;
}

static Term tls_recv_more(Env e, IoWork* w) {
  TlsConn* x = (TlsConn*)w->data;
  if (tls_recv_step(x) == 1) {
    return io_wait_on(w, x->fd, x->want, x->deadline, tls_recv_more);
  }
  Term t = x->len > 0 ? io_done(e, io_list(e, x->out, x->len))
    : x->phase == TLS_ENDED ? io_done(e, term_pak(CID(Nil), 0))
    : io_fail(e, x->code, x->text);
  free(x->out);
  x->out  = NULL;
  x->len  = 0;
  x->busy = 0;
  if (x->closing) {
    tls_conn_free(x);
  }
  return t;
}

// f: conn, max.
Term tls_recv_run(Env e, Term* f, IoWork* w) {
  TlsConn* x = tls_conns_find((u32)f[0]);
  u32      n = (u32)f[1];
  if (x == NULL) {
    return io_fail(e, EBADF, "no open TLS connection has this handle");
  }
  if (x->busy) {
    return io_fail(e, EBUSY, "another Tls.recv is waiting on this connection");
  }
  if (n == 0) {
    return io_fail(e, EINVAL, "a read of 0 bytes");
  }
  if (x->phase == TLS_ENDED) {
    return io_done(e, term_pak(CID(Nil), 0));
  }
  if (x->phase == TLS_BROKEN) {
    return io_fail(e, x->code, x->text);
  }
  x->max  = n < TLS_READ_MAX ? n : TLS_READ_MAX;
  x->out  = io_mem(malloc(x->max));
  x->len  = 0;
  x->busy = 1;
  tls_clock(x);
  w->data = (char*)x;
  return tls_recv_more(e, w);
}

static void __attribute__((constructor)) tls_recv_use(void) {
  io_eff(CID(Tls.recv), tls_recv_run, 0);
}

#endif

// Tls.close
// ---------

#ifdef CID(Tls.close)

// f: conn. An unknown handle is a no-op; a connection a Tls.recv is parked
// on leaves the table now and is freed when that read ends.
Term tls_close_run(Env e, Term* f, IoWork* w) {
  TlsConn* x = tls_conns_find((u32)f[0]);
  if (x != NULL) {
    tls_conns_drop(x);
    if (x->busy) {
      x->closing = 1;
    } else {
      tls_conn_free(x);
    }
  }
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) tls_close_use(void) {
  io_eff(CID(Tls.close), tls_close_run, 0);
}

#endif
