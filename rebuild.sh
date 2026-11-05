#!/usr/bin/env bash
# Rebuild only the stated atlas proof package, without network or installation.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${LEAN_BIN:?Set LEAN_BIN to the verified Lean 4.34.1 binary}"
: "${MATHLIB_DIR:?Set MATHLIB_DIR to the pinned Mathlib checkout with dependencies/cache}"
export PATH="$(dirname "$LEAN_BIN"):$PATH"
test "$(git -C "$MATHLIB_DIR" rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
test "$(sha256sum "$LEAN_BIN" | cut -d' ' -f1)" = e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
"$LEAN_BIN" --version | grep -F 'version 4.34.1,' | grep -F 5045d0056413266e57c625dcd7c365b10e377c52
BASE_PATH="$(cd "$MATHLIB_DIR" && env -u LEAN_PATH lake env printenv LEAN_PATH)"
mkdir -p "$HERE/build" "$HERE/verification/rebuild"
export LEAN_PATH="$HERE/build:$BASE_PATH"
printf '%s\n' "$LEAN_PATH" > "$HERE/verification/rebuild/lean-path.txt"
while read -r mod; do
  "$LEAN_BIN" -j2 -R "$HERE/src" -o "$HERE/build/$mod.olean" "$HERE/src/$mod.lean" \
    > "$HERE/verification/rebuild/$mod.log" 2>&1
  printf 'PASS %s\n' "$mod"
done < "$HERE/modules.txt"
"$LEAN_BIN" -j2 -R "$HERE/src" "$HERE/src/AuditAll.lean" > "$HERE/verification/rebuild/AuditAll.log" 2>&1
printf 'PASS AuditAll\n'
"$LEAN_BIN" -j2 -R "$HERE/src" "$HERE/src/RuntimeProbes.lean" > "$HERE/verification/rebuild/RuntimeProbes.log" 2>&1
printf 'PASS RuntimeProbes\n'
