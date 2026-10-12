#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
# Every proof module must expose its private helpers to the audit as well.
shopt -s globstar nullglob
for source in MMRank/**/*.lean; do
  module="${source%.lean}"
  module="${module//\//.}"
  if ! grep -Fxq "import all $module" scripts/Audit.lean; then
    echo "Missing full audit import for $module in scripts/Audit.lean" >&2
    exit 1
  fi
done
lake env lean scripts/Audit.lean
