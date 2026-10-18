#!/usr/bin/env bash
# The whole local gate, in the order CI runs it. The verification gate
# (scripts/Axioms.lean) checks every declaration on the compiled environment.
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
lake env lean --run scripts/Axioms.lean "$LIB"
lake env lean --run scripts/Axioms.lean Examples

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
