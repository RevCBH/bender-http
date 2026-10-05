import Base

# Host name resolution through the OS resolver (getaddrinfo), so /etc/hosts,
# nsswitch, search domains and systemd-resolved apply as for any C program.
# Base has no DNS (bendlang/bend WONTFIX, #846), and Base's TCP.connect takes
# only a dotted-quad IPv4 address, so this answers IPv4 addresses only: the
# distinct ones, in the resolver's order, at most 16. An empty name or one
# holding a NUL fails with EINVAL; a name with no IPv4 address fails with
# ENOENT. The error text is the resolver's own (gai_strerror).
#
# A canonical dotted quad (`10.0.0.1`) answers itself. Any other host the
# resolver would read as an IPv4 address (inet_aton's forms: octal
# `010.0.0.1`, which is 8.0.0.1, hex `0x7f.1`, short `127.1`, a bare number
# `2130706433`) fails with EINVAL before any lookup, so a host never reaches
# an address its text does not spell (RFC 3986 §7.4). A trailing dot makes a
# name (`127.1.` goes to DNS). The lookup has no timeout of its own: the
# resolver's settings bound it.
#
# This is the library's only foreign effect besides TLS: nothing a law imports
# may import this file.
def Dns.lookup(host: String) -> IO(Result<&1, &1, U32 & String, List<&2, String>>):
  import "./dns.c"
  import "./dns.js"
