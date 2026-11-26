#!/usr/bin/env bash
# Compile every on-chain program (upstream examples + LEMMA programs) to sBPF `.so` in build/.
# The list of LEMMA programs lives in programs.txt: one `<Module> <entrypoint decl> <out-name>` per line.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
fail=0
while read -r mod decl out; do
  [[ -z "${mod:-}" || "$mod" == \#* ]] && continue
  if lake exe lean-svm build "$mod" "$decl" -o "build/$out.so" > "build/$out.log" 2>&1; then
    printf "  %-28s %8s bytes\n" "$out.so" "$(stat -c%s "build/$out.so")"
  else
    echo "  FAILED: $mod $decl"; tail -5 "build/$out.log"; fail=1
  fi
done < programs.txt
exit $fail
