import Base

# HTTPS connections over OpenSSL 3, loaded at run time with dlopen (no
# linker flags; libssl.so.3 / libcrypto.so.3 on Linux, Homebrew's
# libssl.3.dylib on macOS). If OpenSSL 3 cannot be loaded, every effect here
# fails with ENOSYS.
#
# Opening a connection:
#
# - connect to `ip` (a dotted-quad IPv4 address) on `port`; a refused
#   connection is ECONNREFUSED;
# - handshake TLS 1.2 or later with SNI = `server_name` (no SNI when the
#   name is itself an IPv4 address), ALPN "http/1.1", and verify the
#   certificate chain against the system trust store and the name against
#   `server_name`. SNI and verification use the name without one trailing
#   dot (`example.com.` is checked as `example.com`, RFC 6066 §3). The name
#   must match a DNS SAN (or an IP SAN, for an address), or the subject CN of
#   a certificate with no DNS SAN; a wildcard counts only as a whole
#   left-most label (`*.example.com`, never `f*.example.com`; RFC 9525 §6.3).
#   A verification failure is EPROTO, and the text is OpenSSL's reason
#   (X509_verify_cert_error_string); any other TLS failure is ECONNABORTED
#   with OpenSSL's error text. Revocation (OCSP, CRL) is not checked;
# - write all of `request`.
#
# Each step (the connect, the handshake, the write, each read) must finish
# within `timeout_ms`, else ETIMEDOUT; the write and the reads restart their
# clock whenever bytes move. 0 means no limit. An empty or NUL-holding
# server_name, one longer than 255 bytes, an ip that is not a dotted quad,
# port 0 or past 65535, or a request value past 255 fails with EINVAL before
# any connection.
#
# Both lanes run the connection on the event loop with a non-blocking
# socket, parking on it while OpenSSL waits for the peer (as Base's TCP
# effects do): a stalled peer holds no thread and blocks no other
# computation, and any number of connections can wait at once.
#
# This file imports foreign code: nothing a law imports may import it.

# One whole exchange: open, then read until the peer closes. A close without
# close_notify after some data counts as the end (many servers do it); before
# any data it is ECONNRESET. More than `max` bytes is EFBIG. The bytes may
# run past the HTTP message (the caller's decoder decides), and a server that
# keeps the connection open costs a full read timeout, so HTTP should use
# Tls.open / Tls.recv / Tls.close and stop reading once the message is
# complete.
def Tls.exchange(server_name: String, ip: String, port: U32, request: List<&2, U32>, max: U32, timeout_ms: U32) -> IO(Result<&1, &1, U32 & String, List<&2, U32>>):
  import "./tls.c"
  import "./tls.js"

# Opens a connection (connect, handshake and verify, write the request; see
# above) and answers its handle, a U32 that is never 0. The connection stays
# open until Tls.close: close every handle Tls.open gives, on every path.
def Tls.open(server_name: String, ip: String, port: U32, request: List<&2, U32>, timeout_ms: U32) -> IO(Result<&1, &1, U32 & String, U32>):
  import "./tls.c"
  import "./tls.js"

# Reads from an open connection: as soon as some bytes arrive, at most `max`
# of them (and at most 1 MiB), each read within the open's timeout_ms
# (ETIMEDOUT). `[]` means the peer ended the stream with close_notify: the
# end of the data, and every later read answers `[]` again. A close without
# close_notify is ECONNRESET, with the text "...without close_notify" once
# some bytes came (the data may be truncated: RFC 9112 §9.8 accepts such an
# end only when the HTTP framing shows the message complete) or "...before
# any response" when none did. A failure right after some bytes comes on the
# next read (the bytes first), and every later read repeats it. An unknown
# or closed handle is EBADF, a second read while one waits on the same
# connection is EBUSY, and `max` 0 is EINVAL.
def Tls.recv(conn: U32, max: U32) -> IO(Result<&1, &1, U32 & String, List<&2, U32>>):
  import "./tls.c"
  import "./tls.js"

# Closes a connection: sends close_notify when the stream is still open,
# then frees it and its socket. An unknown or closed handle is a no-op.
def Tls.close(conn: U32) -> IO(Unit):
  import "./tls.c"
  import "./tls.js"
