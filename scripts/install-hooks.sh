#!/usr/bin/env bash
# Point git at the repository's versioned hooks (.githooks/). Local, per-clone setting only.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
git config core.hooksPath .githooks
echo "hooks installed: core.hooksPath = .githooks"
