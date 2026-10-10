#!/usr/bin/env bash
# Statement-integrity check (modelled on anthropics/formal-math / Comparator):
#  (a) every spec declaration in JacobianChallenge/Basic.lean still has exactly
#      the frozen statement recorded in scripts/frozen/statements.txt;
#  (b) every spec declaration depends only on the standard axioms
#      propext, Classical.choice, Quot.sound (no sorryAx, no custom axioms,
#      no Lean.ofReduceBool / native_decide).
# Usage: scripts/check_statement.sh            # check
#        scripts/check_statement.sh --freeze   # (re)write the frozen file — review the diff!
# Local use on the Mac Studio: LAKE="$HOME/.claude/bin/lakelock lake" scripts/check_statement.sh
set -uo pipefail
cd "$(dirname "$0")/.."
LAKE=${LAKE:-lake}
FROZEN=scripts/frozen/statements.txt
OUT=$(mktemp)
$LAKE env lean scripts/CheckStatement.lean > "$OUT" 2>&1
rc=$?
if [ $rc -ne 0 ] || ! grep -qE "(^|: )STMT " "$OUT"; then
  cat "$OUT"; echo "FAIL: CheckStatement.lean did not elaborate"; exit 2
fi
# keep only our STMT/AXIOMS lines (strip any "file:line:col: info: " prefix)
grep -oE '(STMT|AXIOMS) .*' "$OUT" > "$OUT.clean"
grep '^STMT ' "$OUT.clean" > "$OUT.stmt"
grep '^AXIOMS ' "$OUT.clean" > "$OUT.ax"
if [ "${1:-}" = "--freeze" ]; then
  cp "$OUT.stmt" "$FROZEN"; echo "Froze $(wc -l < "$FROZEN") statements to $FROZEN"; exit 0
fi
status=0
echo "== (a) statement match against $FROZEN"
if diff -u "$FROZEN" "$OUT.stmt"; then
  echo "PASS: all $(wc -l < "$FROZEN") frozen statements match"
else
  echo "FAIL: statements differ from frozen copy"; status=1
fi
echo "== (b) axiom audit (allowed: propext, Classical.choice, Quot.sound)"
bad=0
while IFS= read -r line; do
  name=${line#AXIOMS }; name=${name%% :: *}; axs=${line#* :: }
  extra=$(echo "$axs" | tr ',' '\n' | sed 's/^ *//' | grep -v -E '^(propext|Classical\.choice|Quot\.sound)?$' | tr '\n' ' ')
  if [ -n "$extra" ]; then echo "FLAG $name uses: $extra"; bad=$((bad+1)); fi
done < "$OUT.ax"
echo "Axioms used across spec: $(sed 's/^.* :: //' "$OUT.ax" | tr ',' '\n' | sed 's/^ *//' | grep -v '^$' | sort -u | tr '\n' ' ')"
if [ $bad -eq 0 ]; then echo "PASS: only standard axioms"; else echo "FAIL: $bad declaration(s) use non-standard axioms"; status=1; fi
exit $status
