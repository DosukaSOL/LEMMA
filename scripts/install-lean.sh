#!/usr/bin/env bash
# Install the exact Lean toolchain named in `lean-toolchain`, verified by SHA-256.
# No elan, no installer script piped to a shell: one pinned release archive and a checksum.
#
# Usage: scripts/install-lean.sh [install-dir]   (prints the bin directory to add to PATH)
set -euo pipefail
cd "$(dirname "$0")/.."
want="$(cat lean-toolchain)"
[[ "$want" == "leanprover/lean4:v4.36.0" ]] || { echo "update the pinned checksum for $want" >&2; exit 1; }
ver="4.36.0"
sha="92a996be487b48e1c2f2985be6b150490475c94d02f5a5e26665a9dab780902a"
dest="${1:-$HOME/.lemma-toolchain}"
bin="$dest/lean-$ver-linux/bin"
if [[ -x "$bin/lean" ]]; then echo "$bin"; exit 0; fi
mkdir -p "$dest"
zip="$dest/lean-$ver-linux.zip"
curl -sSLf -o "$zip" "https://github.com/leanprover/lean4/releases/download/v$ver/lean-$ver-linux.zip"
echo "$sha  $zip" | sha256sum -c - >&2
python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).extractall(sys.argv[2])" "$zip" "$dest"
rm -f "$zip"
chmod -R +x "$bin"
echo "$bin"
