BEND ?= bend
PREFIX ?= /usr/local
BINDIR ?= $(PREFIX)/bin

.PHONY: all install clean test test-offline
all: bender-http

bender-http: cli.bend main.bend $(wildcard src/*.bend src/*.c src/*.js ../dns/main.bend ../dns/src/*.bend ../dns/src/*.c ../dns/src/*.js)
	$(BEND) cli.bend -o $@

install: bender-http
	install -Dm755 bender-http "$(DESTDIR)$(BINDIR)/bender-http"

clean:
	rm -f bender-http

test-offline:
	BEND="$(BEND)" bash tests/cli_offline.sh

test: test-offline
	BEND="$(BEND)" bash tests/cli_test.sh
