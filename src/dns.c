// DNS
// ===

#include <netdb.h>

// getaddrinfo blocks, so it runs on an IO helper thread (io_work): the call
// fills a DnsLookup with up to DNS_LOOKUP_MAX distinct IPv4 addresses, and the
// pack, back on the loop, turns them into a List<String> in resolver order.
#define DNS_LOOKUP_MAX 16
#define DNS_NUMERIC_WHY \
  "a numeric host that is not a dotted-quad IPv4 address (the resolver would read it as octal, hex or a short form)"

typedef struct {
  char* host;
  u32   size;
  int   rc;
  int   sys;
  char  addr[DNS_LOOKUP_MAX][INET_ADDRSTRLEN];
} DnsLookup;

// The resolver's EAI_* codes differ by platform; the Result carries an errno
// value instead, and the text says what the resolver said.
static u32 dns_lookup_code(DnsLookup* d) {
  switch (d->rc) {
    case 0:          return ENOENT;
    case EAI_SYSTEM: return d->sys != 0 ? (u32)d->sys : EIO;
    case EAI_AGAIN:  return EAGAIN;
    case EAI_MEMORY: return ENOMEM;
    case EAI_FAIL:   return EIO;
    case EAI_NONAME: return ENOENT;
#if defined(EAI_NODATA) && EAI_NODATA != EAI_NONAME
    case EAI_NODATA: return ENOENT;
#endif
    default:         return EINVAL;
  }
}

static void dns_lookup_call(IoWork* w) {
  DnsLookup*       d = (DnsLookup*)w->data;
  struct addrinfo  hints;
  struct addrinfo* res = NULL;
  memset(&hints, 0, sizeof hints);
  hints.ai_family   = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  d->rc  = getaddrinfo(d->host, NULL, &hints, &res);
  d->sys = d->rc == EAI_SYSTEM ? errno : 0;
  for (struct addrinfo* ai = res; ai != NULL && d->size < DNS_LOOKUP_MAX; ai = ai->ai_next) {
    char* at = d->addr[d->size];
    if (ai->ai_family != AF_INET || inet_ntop(AF_INET,
        &((struct sockaddr_in*)ai->ai_addr)->sin_addr, at, INET_ADDRSTRLEN) == NULL) {
      continue;
    }
    u32 seen = 0;
    while (seen < d->size && strcmp(d->addr[seen], at) != 0) {
      seen += 1;
    }
    d->size += seen == d->size;
  }
  if (res != NULL) {
    freeaddrinfo(res);
  }
}

static Term dns_lookup_pack(Env e, IoWork* w) {
  DnsLookup* d = (DnsLookup*)w->data;
  Term       r;
  if (d->rc != 0 || d->size == 0) {
    const char* text = d->rc == 0 ? "no IPv4 address for this name"
      : d->rc == EAI_SYSTEM ? NULL : gai_strerror(d->rc);
    r = io_fail(e, dns_lookup_code(d), text);
  } else {
    Term xs = term_pak(CID(Nil), 0);
    for (u32 i = d->size; i > 0; i -= 1) {
      xs = io_node(e, CID(Con), io_str(e, d->addr[i - 1], strlen(d->addr[i - 1])), xs);
    }
    r = io_done(e, xs);
  }
  free(d->host);
  free(d);
  return r;
}

// True when the resolver would read host as an IPv4 address (getaddrinfo
// with AI_NUMERICHOST: inet_aton's forms, so octal "010.0.0.1", hex
// "0x7f.1", short "127.1" and a bare 32-bit number "2130706433") but host is
// not the canonical dotted quad io_sys_addr takes. Such a host would reach
// an address its text does not spell, so the lookup refuses it. A numeric
// parse makes no query, so this runs on the loop.
static int dns_lookup_noncanonical(const char* host) {
  struct addrinfo    hints;
  struct addrinfo*   res = NULL;
  struct sockaddr_in at;
  memset(&hints, 0, sizeof hints);
  hints.ai_family   = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags    = AI_NUMERICHOST;
  if (getaddrinfo(host, NULL, &hints, &res) != 0) {
    return 0;
  }
  freeaddrinfo(res);
  return io_sys_addr(host, 0, &at) != 0;
}

Term dns_lookup_run(Env e, Term* f, IoWork* w) {
  u64   len  = 0;
  char* host = io_cstr(e, f[0], &len);
  if (len == 0 || io_nul(host, len)) {
    free(host);
    return io_fail(e, EINVAL, NULL);
  }
  if (dns_lookup_noncanonical(host)) {
    free(host);
    return io_fail(e, EINVAL, DNS_NUMERIC_WHY);
  }
  DnsLookup* d = (DnsLookup*)io_mem(calloc(1, sizeof(DnsLookup)));
  d->host = host;
  w->data = (char*)d;
  return io_work(w, dns_lookup_call, dns_lookup_pack);
}

static void __attribute__((constructor)) dns_lookup_use(void) {
  io_eff(CID(Dns.lookup), dns_lookup_run, 0);
}
