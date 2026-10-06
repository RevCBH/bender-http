"""Exercise the public resolver and CLI against local ephemeral servers."""
import contextlib
import http.server
import pathlib
import os
import ssl
import socketserver
import struct
import subprocess
import sys
import threading
import time

# Use the DNS package's tested wire fixture helpers.
sys.path.insert(0, str(pathlib.Path('../dns/tests').resolve()))
from dns_server import frame, parse_query, read_exact, response, rr, wire_name

out = pathlib.Path(sys.argv[1])
failures = 0
requests = []
queries = []
binary = bytes(range(256)) * 256


class DNSHandler(socketserver.BaseRequestHandler):
    def handle(self):
        prefix = read_exact(self.request, 2)
        if prefix is None:
            return
        msg = read_exact(self.request, struct.unpack('!H', prefix)[0])
        if msg is None:
            return
        qid, flags, labels, qtype, qclass, question = parse_query(msg)
        name = b'.'.join(labels).decode().lower()
        queries.append(name)
        if name == 'slow.test':
            time.sleep(4)
            return
        rcode, answers = 0, []
        if name == 'alias.test':
            answers = [rr(None, 5, wire_name('x.test'))]
        elif name == 'nodata.test':
            pass
        elif name not in ('x.test', 'other.test'):
            rcode = 3
        else:
            answers = [rr(None, 1, bytes([127, 0, 0, 1]))]
        self.request.sendall(frame(response(qid, flags, question, rcode, answers)))


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


class HTTPHandler(http.server.BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'

    def log_message(self, *_):
        pass

    def handle_request(self):
        body = self.rfile.read(int(self.headers.get('Content-Length', 0)))
        requests.append((self.command, self.path, self.headers, body))
        status, data, headers = 200, b'hello\n', []
        if self.path == '/binary':
            data = binary
        elif self.path == '/echo':
            data = body
        elif self.path == '/redirect':
            status, data, headers = 302, b'', [('Location', '/binary')]
        elif self.path == '/loop':
            status, data, headers = 302, b'', [('Location', '/loop')]
        elif self.path == '/cross':
            status, data, headers = 302, b'', [('Location', f'http://other.test:{self.server.server_port}/')]
        elif self.path == '/404':
            status, data = 404, b'missing\n'
        self.send_response(status)
        for key, value in headers:
            self.send_header(key, value)
        self.send_header('Content-Length', str(len(data)))
        self.end_headers()
        if self.command != 'HEAD':
            self.wfile.write(data)

    do_GET = do_POST = do_PUT = do_HEAD = handle_request


def expect(label, args, code=0, stdout=None, contains=None, stderr=None, limit=None):
    global failures
    started = time.monotonic()
    try:
        result = subprocess.run(command + args, capture_output=True, timeout=20)
        elapsed = time.monotonic() - started
        assert result.returncode == code, f'exit {result.returncode}: {result.stderr!r}'
        if stdout is not None:
            assert result.stdout == stdout, f'stdout ({len(result.stdout)} bytes): {result.stdout[:200]!r}'
        if contains is not None:
            assert contains in result.stdout, f'stdout: {result.stdout[:200]!r}'
        if stderr is not None:
            assert stderr in result.stderr, f'stderr: {result.stderr!r}'
        if limit is not None:
            assert elapsed < limit, f'elapsed {elapsed:.2f}s, limit {limit}s'
        return result
    except (AssertionError, subprocess.TimeoutExpired) as error:
        print(f'FAIL [{lane}] {label}: {error}', flush=True)
        failures += 1
    finally:
        if failures == before:
            print(f'PASS [{lane}] {label}', flush=True)


with contextlib.ExitStack() as stack:
    dns = stack.enter_context(Server(('127.0.0.1', 0), DNSHandler))
    plain = stack.enter_context(http.server.ThreadingHTTPServer(('127.0.0.1', 0), HTTPHandler))
    subprocess.run(['openssl', 'req', '-x509', '-newkey', 'rsa:2048', '-nodes',
                    '-keyout', str(out / 'key.pem'), '-out', str(out / 'cert.pem'),
                    '-subj', '/CN=x.test', '-addext', 'subjectAltName=DNS:x.test', '-days', '1'],
                   check=True, capture_output=True)
    tls = stack.enter_context(http.server.ThreadingHTTPServer(('127.0.0.1', 0), HTTPHandler))
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.load_cert_chain(out / 'cert.pem', out / 'key.pem')
    tls.socket = ctx.wrap_socket(tls.socket, server_side=True)
    os.environ['SSL_CERT_FILE'] = str(out / 'cert.pem')
    for server in (dns, plain, tls):
        threading.Thread(target=server.serve_forever, daemon=True).start()
        stack.callback(server.shutdown)
    dns_args = ['--dns-server', '127.0.0.1', '--dns-port', str(dns.server_address[1])]
    url = f'http://x.test:{plain.server_port}'
    for lane, command, resolver in (
        ('c', [str(out / 'bender-http')], [str(out / 'resolver')]),
        ('js', [sys.argv[2], 'cli.bend', '--'], [sys.argv[2], 'tests/resolver_local.bend', '--']),
    ):
        def check(*args, **kwargs):
            global before
            before = failures
            return expect(*args, **kwargs)

        check('help', ['--help'], contains=b'usage: bender-http')
        check('no URL', [], 1, b'', stderr=b'usage:')
        check('unknown option', ['--bogus'], 1, b'', stderr=b'unknown option')
        check('multiple URLs', [url, url], 1, b'', stderr=b'more than one URL')
        for flag in ('-o', '-H', '-d', '-X', '--timeout', '--max', '--dns-server', '--dns-port'):
            check(f'missing {flag}', [flag], 1, b'', stderr=b'missing its value')
        for flag, value in (('--timeout', '-1'), ('--timeout', '4294967296'), ('--max', 'no'),
                            ('--max', '4294967296'), ('--dns-port', '0'), ('--dns-port', '65536'),
                            ('--dns-server', '127.1')):
            check(f'invalid {flag} {value}', [flag, value, url], 1, b'')
        check('malformed header', ['-H', 'oops', url], 1, b'', stderr=b'bad header')
        check('bad URL', ['file:///tmp/a'], 1, b'', stderr=b'bad URL')
        check('native DNS + GET', dns_args + [url + '/'], stdout=b'hello\n')
        assert requests[-1][2]['Host'] == f'x.test:{plain.server_port}'
        secure = f'https://x.test:{tls.server_port}'
        check('HTTPS with native DNS and hostname verification', dns_args + [secure], stdout=b'hello\n')
        check('HTTPS binary', dns_args + [secure + '/binary'], stdout=binary)
        check('HTTPS wrong hostname', dns_args + [secure.replace('x.test', 'other.test')],
              1, b'', stderr=b'TLS')
        check('binary stdout', dns_args + [url + '/binary'], stdout=binary)
        dest = out / f'{lane}.bin'
        check('binary file', dns_args + ['-o', str(dest), url + '/binary'], stdout=b'')
        assert dest.read_bytes() == binary
        check('stdout alias', dns_args + ['-o', '-', url], stdout=b'hello\n')
        check('include headers', dns_args + ['-i', url], contains=b'HTTP/1.1 200 OK\r\n')
        result = check('HEAD', dns_args + ['-I', url], contains=b'Content-Length: 6\r\n')
        assert result.stdout.endswith(b'\r\n\r\n') and requests[-1][0] == 'HEAD'
        check('POST UTF-8', dns_args + ['-H', 'X-Test: a:b', '-d', 'h\u00e9', url + '/echo'], stdout='h\u00e9'.encode())
        assert requests[-1][0] == 'POST' and requests[-1][2]['X-Test'] == 'a:b'
        check('explicit method', dns_args + ['-X', 'PUT', '-d', 'hi', url + '/echo'], stdout=b'hi')
        assert requests[-1][0] == 'PUT'
        check('redirect disabled', dns_args + [url + '/redirect'], stdout=b'')
        check('redirect followed', dns_args + ['-L', url + '/redirect'], stdout=binary)
        check('redirect limit', dns_args + ['-L', url + '/loop'], 1, b'', stderr=b'more than 10 redirects')
        check('cross origin', dns_args + ['-L', '-H', 'Authorization: secret', '-H', 'Cookie: secret', url + '/cross'], stdout=b'hello\n')
        assert 'Authorization' not in requests[-1][2] and 'Cookie' not in requests[-1][2]
        check('404 body by default', dns_args + [url + '/404'], stdout=b'missing\n')
        dest.write_bytes(b'preserve')
        check('fail HTTP status', dns_args + ['-f', '-o', str(dest), url + '/404'], 1, b'', stderr=b'HTTP error 404')
        assert dest.read_bytes() == b'preserve'
        check('response limit', dns_args + ['--max', '64', url + '/binary'], 1, b'', stderr=b'larger than the limit')
        check('output error', dns_args + ['-o', str(out / 'absent' / 'file'), url], 1, b'', stderr=b'output error')
        check('CNAME lookup', dns_args + [url.replace('x.test', 'alias.test')], stdout=b'hello\n')
        check('NXDOMAIN', dns_args + [url.replace('x.test', 'missing.test')], 1, b'', stderr=b'NXDOMAIN')
        check('NODATA', dns_args + [url.replace('x.test', 'nodata.test')], 1, b'', stderr=b'no IPv4 address')
        for scheme in ('http', 'https'):
            check(f'DNS timeout {scheme}', dns_args + ['--timeout', '100', url.replace('x.test', 'slow.test').replace('http:', scheme + ':')],
                  1, b'', stderr=b'timed out', limit=3)
        saved = command
        command = resolver
        check('public resolver API', [str(dns.server_address[1])], contains=b'PASS whole DNS lookup deadline', limit=4)
        command = saved

assert 'x.test' in queries and 'alias.test' in queries
if failures:
    sys.exit(f'{failures} HTTP integration tests failed')
print('ALL HTTP INTEGRATION TESTS PASS')
