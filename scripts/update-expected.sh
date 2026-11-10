#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Assay Examples
for f in AssayTest/*.lean; do
  header=$(sed -n '/^import /p' "$f")
  opts=$(sed -n '/^set_option /p' "$f")
  cmd=$(grep '^#assay' "$f")
  pre() {
    printf '%s\n\n' "$header"
    if [ -n "$opts" ]; then printf '%s\n' "$opts"; fi
  }
  { pre; printf '#guard_msgs in\n%s\n' "$cmd"; } > "$f"
  out=$(lake env lean "$f" 2>&1 | awk 'f { print substr($0, 3) } /does not match generated message:/ { f = 1; getline }' || true)
  { pre; printf '/--\n%s\n-/\n#guard_msgs in\n%s\n' "$out" "$cmd"; } > "$f"
done
