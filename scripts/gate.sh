#!/usr/bin/env bash
# Gate for nut-lean: build the package and reject proof holes or kernel
# escape hatches in the Lean sources.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
if [[ ! -x "$LAKE_BIN" ]]; then
  LAKE_BIN="$(command -v lake)"
fi

"$LAKE_BIN" build

status=0
while IFS= read -r -d '' file; do
  if grep -nE '\<(sorry|admit|axiom|native_decide)\>' "$file"; then
    echo "GATE FAIL: forbidden proof token in $file" >&2
    status=1
  fi
done < <(find . -path './.lake' -prune -o -name '*.lean' -print0)

if [[ "$status" -ne 0 ]]; then
  echo "GATE FAIL" >&2
  exit 1
fi

echo "GATE OK"
