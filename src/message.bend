import Base
import ./bytes.bend as B

# The data an HTTP/1.1 exchange is made of. Every number is a Nat (ports,
# statuses, lengths): Nat arithmetic is native at runtime, and the checker
# reasons about it by induction, which it cannot do for U32's bit words.

type Method is Data:
  GET{}
  HEAD{}
  POST{}
  PUT{}
  DELETE{}
  PATCH{}
  OPTIONS{}
  Other{name: String}       # must be a token (validated by request_ok)

type Scheme is Data:
  Http{}
  Https{}

# An absolute http(s) URL, as the client uses it: the host as written (a
# name or a dotted-quad IPv4 address, lowercase), the port (always present;
# the scheme's default when the URL names none), and the request target in
# origin form (a path starting with "/", with its "?query"; never a fragment).
type Url is Data:
  Url{scheme: Scheme, host: String, port: Nat, target: String}

# One header field, name and value as sent or received. Names keep their
# case; lookups ignore it.
type Header is Data:
  Header{name: String, value: String}

type Request is Data:
  Request{method: Method, url: Url, headers: List<&2, Header>, body: List<&2, U32>}

type Version is Data:
  Http10{}
  Http11{}

type Response is Data:
  Response{version: Version, status: Nat, reason: String, headers: List<&2, Header>, body: List<&2, U32>}

# Why a response could not be read.
type ParseError is Data:
  BadStatusLine{}           # not "HTTP/1.x SP 3DIGIT SP reason CRLF"
  BadVersion{}              # a version other than HTTP/1.0 or HTTP/1.1
  BadHeader{}               # a field line that is not "token: value CRLF"
  BadLength{}               # Content-Length not one decimal (or several equal ones)
  ConflictingFraming{}      # Transfer-Encoding and Content-Length together
  UnsupportedEncoding{}     # a transfer coding other than chunked alone
  BadChunk{}                # a malformed chunk size, extension or terminator
  UnexpectedUpgrade{}       # a 101 Switching Protocols the client never asked for
  Incomplete{}              # the connection closed before the message ended
  TooLarge{}                # the response is longer than the limit

# What a decoded response leaves: the response, and the bytes after it
# (none for a response delimited by the connection's close).
type Decoded is Data:
  Decoded{response: Response, rest: List<&2, U32>}

# Why a request failed. The codes and messages are errno values and texts,
# as Base's effects report them.
type Error is Data:
  BadUrl{reason: String}
  BadRequest{reason: String}
  NoAddress{host: String}
  Dns{code: U32, message: String}
  Connect{code: U32, message: String}
  Io{code: U32, message: String}
  Timeout{}
  Tls{code: U32, message: String}
  Parse{error: ParseError}
