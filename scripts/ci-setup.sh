#!/usr/bin/env bash
# Install the pinned toolchain for CI on a stock Linux x86_64 runner: Bend 2.0.32
# and Lean 4.34.0 (for `bend --verdict`), sha256-verified, under $TOOLS
# (default ~/.cache/bend-toolchain), and put them on PATH (via $GITHUB_PATH when
# set). Rerunning with the files cached does no download.
set -euo pipefail
BEND_VERSION=2.0.32
BEND_SHA=5c365ddb12954d0933cef751802e0f7d9875f842edcb80f9661f89cd1a9ff7b6
LEAN_VERSION=4.34.0
LEAN_SHA=caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b
TOOLS="${TOOLS:-$HOME/.cache/bend-toolchain}"
mkdir -p "$TOOLS"
fetch() { # url sha dest
  [[ -f $3 ]] && printf '%s  %s\n' "$2" "$3" | sha256sum -c --quiet - && return
  curl --proto '=https' --tlsv1.2 -fsSL --retry 3 -o "$3.part" "$1"
  printf '%s  %s\n' "$2" "$3.part" | sha256sum -c --quiet -
  mv "$3.part" "$3"
}
if [[ ! -x $TOOLS/bend-$BEND_VERSION/bin/bend ]]; then
  fetch "https://github.com/bendlang/bend/releases/download/v$BEND_VERSION/bend-$BEND_VERSION-linux-x64.tar.gz" \
    "$BEND_SHA" "$TOOLS/bend.tar.gz"
  rm -rf "$TOOLS/bend-$BEND_VERSION" "$TOOLS/bend"
  tar -xzf "$TOOLS/bend.tar.gz" -C "$TOOLS" && mv "$TOOLS/bend" "$TOOLS/bend-$BEND_VERSION"
  rm -f "$TOOLS/bend.tar.gz"
fi
if [[ ! -x $TOOLS/lean-$LEAN_VERSION/bin/lean ]]; then
  fetch "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.tar.zst" \
    "$LEAN_SHA" "$TOOLS/lean.tar.zst"
  rm -rf "$TOOLS/lean-$LEAN_VERSION"
  tar --zstd -xf "$TOOLS/lean.tar.zst" -C "$TOOLS" && mv "$TOOLS/lean-$LEAN_VERSION-linux" "$TOOLS/lean-$LEAN_VERSION"
  rm -f "$TOOLS/lean.tar.zst"
fi
# Only these on PATH: Lean's bin/ also holds its own clang (no system
# headers), which must not shadow the system clang that native builds use.
mkdir -p "$TOOLS/bin"
ln -sfn "$TOOLS/bend-$BEND_VERSION/bin/bend" "$TOOLS/bin/bend"
for tool in lean lake leanc; do ln -sfn "$TOOLS/lean-$LEAN_VERSION/bin/$tool" "$TOOLS/bin/$tool"; done
[[ -n ${GITHUB_PATH:-} ]] && echo "$TOOLS/bin" >> "$GITHUB_PATH"
export PATH="$TOOLS/bin:$PATH"
[[ -n ${GITHUB_ENV:-} ]] && echo 'BEND_NO_TELEMETRY=1' >> "$GITHUB_ENV"
BEND_NO_TELEMETRY=1 bend version
lean --version
