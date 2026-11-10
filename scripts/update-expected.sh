#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Assay Examples
for f in AssayTest/*.lean; do
  header=$(sed -n '/^import /p' "$f")
  cmd=$(grep '^#assay' "$f")
  printf '%s\n\n#guard_msgs in\n%s\n' "$header" "$cmd" > "$f"
  out=$(lake env lean "$f" 2>&1 | awk 'f { print substr($0, 3) } /does not match generated message:/ { f = 1; getline }' || true)
  printf '%s\n\n/--\n%s\n-/\n#guard_msgs in\n%s\n' "$header" "$out" "$cmd" > "$f"
done
