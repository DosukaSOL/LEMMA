#!/usr/bin/env bash
# Fast textual guard against proof holes in LEMMA's own Lean sources. The authoritative check is
# `lake exe lemma-audit` (it inspects the axioms of every compiled theorem); this script catches
# mistakes before a build, e.g. in the pre-commit hook.
#
# Usage: scripts/check-proof-holes.sh [--staged]
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
if [[ "${1:-}" == "--staged" ]]; then
  mapfile -t files < <(git diff --cached --name-only --diff-filter=ACM -- 'Lemma/*.lean' 'Lemma.lean' 'tests/*.lean')
else
  mapfile -t files < <(git ls-files -- 'Lemma/*.lean' 'Lemma.lean' 'tests/*.lean')
fi
[[ ${#files[@]} -eq 0 ]] && exit 0
# Strip line comments and block comments before matching, so documentation may mention the words.
bad=0
for f in "${files[@]}"; do
  [[ -f "$f" ]] || continue
  hits=$(python3 - "$f" <<'PY'
import re, sys
src = open(sys.argv[1], encoding="utf-8").read()
src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
src = re.sub(r"--[^\n]*", "", src)
src = re.sub(r'"(?:\\.|[^"\\])*"', '""', src)
pat = re.compile(r"\b(sorry|admit|native_decide|bv_decide|implemented_by|extern)\b|^\s*(private\s+)?axiom\b|\bunsafe\b", re.M)
for i, line in enumerate(src.splitlines(), 1):
    if pat.search(line):
        print(f"{sys.argv[1]}:{i}: {line.strip()}")
PY
)
  if [[ -n "$hits" ]]; then echo "$hits"; bad=1; fi
done
if [[ $bad -ne 0 ]]; then
  echo "check-proof-holes: forbidden construct found (sorry/admit/axiom/native_decide/bv_decide/unsafe/extern)" >&2
  exit 1
fi
echo "check-proof-holes: OK (${#files[@]} files)"
