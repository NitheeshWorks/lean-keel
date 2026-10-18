#!/usr/bin/env bash
# The whole local gate, in the order CI runs it. The verification gate
# (scripts/Axioms.lean, `lake exe axioms`) checks every declaration of the
# library; it is stack-tools/Axioms.lean, copied byte for byte and pinned by
# scripts/Axioms.sha256.
# Exits on the first failure.
#
#   scripts/check.sh            # everything
#   scripts/check.sh --quick    # build and the verification gate (no tests)
#   scripts/check.sh --pbt      # everything, plus the plausible suite
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIB=Keel

echo "== build =="
lake build

echo "== verification gate =="
echo "$(cat scripts/Axioms.sha256)  scripts/Axioms.lean" | sha256sum --check --quiet
lake exe axioms "$LIB"
lake exe axioms Examples

[[ "${1:-}" == "--quick" ]] && exit 0

echo "== property tests =="
lake exe props

echo "== conformance =="
lake exe conformance

echo "== examples =="
lake exe examples > /dev/null

echo "== bench (routing time on long paths) =="
lake exe bench

echo "== traceability =="
python3 scripts/traceability-check.py

if [[ "${1:-}" == "--pbt" ]]; then
  echo "== plausible =="
  (cd tests/pbt && lake build && ./.lake/build/bin/pbt)
fi
echo "all clean"
