#!/usr/bin/env python3
"""Local TLS servers for tests/tls_live.bend (run by tests/tls_live.sh).

  tls_server.py DIR BASE_PORT

Makes a self-signed certificate for localhost and 127.0.0.1 in DIR
(DIR/cert.pem), and one for the names DNS:f*.example.test (a partial-label
wildcard, which the client must refuse) and DNS:*.wild.test (DIR/wild.pem);
DIR/trust.pem holds both, and the client trusts it through SSL_CERT_FILE.
Then serves one mode per port on 127.0.0.1, BASE_PORT + index in MODES,
until killed. Prints "ready" once every port listens.
"""
import os
import socket
import ssl
import struct
import subprocess
import sys
import threading
import time
import warnings

MODES = [
    "ok",        # 0: a 5-byte response, then close_notify
    "eof",       # 1: the same, then a TCP close with no close_notify
    "big",       # 2: 100000 bytes, then close_notify
    "silent",    # 3: handshake, read the request, then say nothing for 10 s
    "nodata",    # 4: handshake, read the request, TCP close, no close_notify
    "empty",     # 5: handshake, read the request, close_notify, no data
    "plain",     # 6: not TLS: a plain HTTP response to the ClientHello
    "stall",     # 7: accept, then never answer the ClientHello
    "echo",      # 8: answer the request's bytes, up to and with "\r\n\r\n"
    "slam",      # 9: handshake, then a TCP close at once (the client's write fails)
    "old",       # 10: TLS 1.1 at most
    "keepalive", # 11: a 5-byte response, then hold the connection open 6 s
    "rst_after", # 12: a 5-byte response, then a TCP reset 0.5 s later
    "cd_fin",    # 13: a body with no length (runs to the close), then a TCP close, no close_notify
    "cd_notify", # 14: the same body, then close_notify
    "wild",      # 15: as ok, with the wildcard certificate
]

RESPONSE = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"
CLOSE_DELIMITED = b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\nPARTIAL-BODY"  # 57 bytes
BIG_HEAD = b"HTTP/1.1 200 OK\r\nContent-Length: 99958\r\n\r\n"
BIG = BIG_HEAD + b"x" * (100000 - len(BIG_HEAD))  # 100000 bytes in all


def make_cert(d, name, cn, san):
    cert, key = os.path.join(d, name + ".pem"), os.path.join(d, name + "_key.pem")
    subprocess.run(
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-days", "2",
         "-subj", "/CN=" + cn, "-addext", "subjectAltName=" + san,
         "-addext", "basicConstraints=critical,CA:TRUE",
         "-keyout", key, "-out", cert],
        check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return cert, key


def read_request(s):
    data = b""
    while b"\r\n\r\n" not in data:
        part = s.recv(65536)
        if not part:
            break
        data += part
    return data


def abort(s):
    # A TCP close with no close_notify: SSLSocket.shutdown drops the TLS
    # state and shuts the socket down without sending an alert.
    try:
        s.shutdown(socket.SHUT_RDWR)
    except OSError:
        pass
    s.close()


def serve_one(mode, conn, ctx):
    conn.settimeout(30)
    if mode == "plain":
        conn.recv(4096)
        conn.sendall(b"HTTP/1.1 400 Bad Request\r\nContent-Length: 0\r\n\r\n")
        conn.close()
        return
    if mode == "stall":
        time.sleep(10)
        conn.close()
        return
    s = ctx.wrap_socket(conn, server_side=True)
    if mode == "slam":
        abort(s)
        return
    req = read_request(s)
    if mode in ("ok", "eof", "big", "echo", "old", "keepalive", "rst_after", "wild"):
        body = {"big": BIG, "echo": req}.get(mode, RESPONSE)
        s.sendall(body)
    if mode in ("cd_fin", "cd_notify"):
        s.sendall(CLOSE_DELIMITED)
    if mode == "silent":
        time.sleep(10)
    if mode == "keepalive":
        time.sleep(6)
    if mode == "rst_after":
        time.sleep(0.5)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
        s.close()
        return
    if mode in ("eof", "nodata", "cd_fin"):
        abort(s)
        return
    try:
        s.unwrap().close()
    except (OSError, ssl.SSLError):
        s.close()


def run(mode, conn, ctx):
    try:
        serve_one(mode, conn, ctx)
    except Exception as e:  # a test client may hang up at any point
        print(mode, "server:", e, file=sys.stderr)
        conn.close()


def serve(mode, lsock, ctx):
    while True:
        conn, _ = lsock.accept()
        threading.Thread(target=run, args=(mode, conn, ctx), daemon=True).start()


def main():
    d, base = sys.argv[1], int(sys.argv[2])
    cert, key = make_cert(d, "cert", "localhost", "DNS:localhost,IP:127.0.0.1")
    wild, wild_key = make_cert(d, "wild", "wild", "DNS:f*.example.test,DNS:*.wild.test")
    with open(os.path.join(d, "trust.pem"), "w") as out:
        for c in (cert, wild):
            with open(c) as f:
                out.write(f.read())
    for i, mode in enumerate(MODES):
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        if mode == "wild":
            ctx.load_cert_chain(wild, wild_key)
        else:
            ctx.load_cert_chain(cert, key)
        if mode == "old":
            try:
                ctx.set_ciphers("DEFAULT:@SECLEVEL=0")
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore", DeprecationWarning)
                    ctx.minimum_version = ssl.TLSVersion.TLSv1
                    ctx.maximum_version = ssl.TLSVersion.TLSv1_1
            except (ValueError, ssl.SSLError) as e:
                print("old: cannot limit to TLS 1.1:", e, file=sys.stderr)
        lsock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        lsock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        lsock.bind(("127.0.0.1", base + i))
        lsock.listen(16)
        threading.Thread(target=serve, args=(mode, lsock, ctx), daemon=True).start()
    print("ready", flush=True)
    while True:
        time.sleep(3600)


if __name__ == "__main__":
    main()
