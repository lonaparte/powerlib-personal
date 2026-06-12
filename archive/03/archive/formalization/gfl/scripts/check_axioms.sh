#!/usr/bin/env bash
# A4 — CI axiom gate for the GFL formalization.
#
# Forces re-elaboration of GFL/Audit.lean and FAILS (non-zero exit) if ANY of:
#   * the build errors out;
#   * any declaration depends on `sorryAx` (a `sorry`/`admit` hole);
#   * any `#print axioms` line reports axioms other than the standard
#       [propext, Classical.choice, Quot.sound];
#   * the number of certified declarations does not equal the number of `#print axioms`
#     directives in Audit.lean (catches a silently dropped / errored audit line).
#
# Usage:  scripts/check_axioms.sh        (run from anywhere; resolves the project root)
set -uo pipefail

cd "$(dirname "$0")/.." || { echo "FAIL: cannot cd to project root"; exit 2; }
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
CLEAN='[propext, Classical.choice, Quot.sound]'

# Force Audit.lean to re-elaborate so the `#print axioms` messages are re-emitted
# (a fully-cached no-op build may print nothing).
rm -f .lake/build/lib/lean/GFL/Audit.olean

echo "==> $LAKE build GFL.Audit"
OUT="$("$LAKE" build GFL.Audit 2>&1)"
STATUS=$?
echo "$OUT"
echo "------------------------------------------------------------"

if [ "$STATUS" -ne 0 ]; then
  echo "FAIL: lake build returned non-zero exit ($STATUS)"; exit 1
fi
if echo "$OUT" | grep -q "error:"; then
  echo "FAIL: build log contains 'error:'"; exit 1
fi
if echo "$OUT" | grep -q "sorryAx"; then
  echo "FAIL: a declaration depends on sorryAx (a sorry/admit hole)"; exit 1
fi

# Every 'depends on axioms:' line must report exactly the clean axiom set.
BAD="$(echo "$OUT" | grep "depends on axioms" | grep -vF "$CLEAN")"
if [ -n "$BAD" ]; then
  echo "FAIL: declaration(s) with non-standard axioms:"; echo "$BAD"; exit 1
fi

EXPECTED="$(grep -c '^#print axioms' GFL/Audit.lean)"
GOT="$(echo "$OUT" | grep -c "depends on axioms")"
if [ "$EXPECTED" -ne "$GOT" ]; then
  echo "FAIL: expected $EXPECTED certified declarations, got $GOT"
  echo "      (a '#print axioms' directive was dropped or errored — no silent exclusion allowed)"
  exit 1
fi

echo "PASS: $GOT/$EXPECTED declarations certify exactly $CLEAN"
echo "      — no sorryAx, no non-standard axioms, no silent exclusion."
