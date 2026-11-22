#!/usr/bin/env bash
# Install elan (which then fetches the toolchain in lean-toolchain) and the harness's npm deps.
set -euo pipefail
cd "$(dirname "$0")/../.."
if ! command -v elan >/dev/null; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  echo "$HOME/.elan/bin" >> "${GITHUB_PATH:-/dev/null}"
  export PATH="$HOME/.elan/bin:$PATH"
fi
elan toolchain install "$(cat lean-toolchain)"
# The harness needs the playwright module to load, but recording and checking use no browser.
PLAYWRIGHT_SKIP_BROWSER_DOWNLOAD=1 npm install --no-audit --no-fund
