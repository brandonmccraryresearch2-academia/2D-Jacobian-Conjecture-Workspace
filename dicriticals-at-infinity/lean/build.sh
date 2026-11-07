#!/usr/bin/env bash
# build.sh -- compile the two-dicritical Lean modules (Lean 4.34.0, Mathlib v4.34.0) and audit them.
#
# Usage: build.sh [LEAN_PROJECT]
#   LEAN_PROJECT is any Lake project with Mathlib v4.34.0 available (default:
#   ../../JC2D-branches_a_b_c_unified/branches_a_b/lean, after
#   `lake exe cache get` there). Nothing is written into it: the .olean files go to a temporary directory.
#
# Steps:
#   1. scan TwoDicritical/*.lean (comments stripped) for sorry, admit, native_decide and the keyword `axiom`
#      anywhere on a line (so `noncomputable axiom`, `protected axiom` and attributes are caught too);
#   2. compile BlockRank, E1Obstruction, BridgeCollapse, CenterHypotheses, OneCenter, E1Keller, E1Valuation, Axioms in this
#      order, each with `lean -o`; any error or "declaration uses sorry" fails;
#   3. check that every `#print axioms` line of Axioms.lean names only propext, Classical.choice, Quot.sound
#      (or a subset).
# Exit status 0 iff all steps pass; 2 if the project has no compiled Mathlib (checked first, so that `lake` does not
# start cloning Mathlib in a fresh checkout). Time on 2 cores (2026-10-13): about 2 min; memory below 2 GB.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
PROJ="${1:-$HERE/../../JC2D-branches_a_b_c_unified/branches_a_b/lean}"
PROJ="$(cd "$PROJ" && pwd)" || { echo "FAIL: no Lean project at $PROJ"; exit 1; }
if [ ! -f "$PROJ/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]; then
  echo "FAIL: no compiled Mathlib in $PROJ (.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean is missing)."
  echo "      Run 'lake exe cache get' in that project first (it fetches Mathlib v4.34.0 with prebuilt .olean files),"
  echo "      or pass a Lake project that already has it: build.sh /path/to/project"
  exit 2
fi
export PATH="$HOME/.elan/bin:$PATH"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
mkdir -p "$OUT/TwoDicritical"
MODULES="BlockRank E1Obstruction BridgeCollapse CenterHypotheses OneCenter E1Keller E1Valuation Axioms"

echo "=== 1. source scan ==="
python3 - "$HERE"/TwoDicritical/*.lean <<'PY' || { echo "FAIL: sorry/admit/native_decide/axiom found"; exit 1; }
import re, sys
bad = 0
for f in sys.argv[1:]:
    s = re.sub(r'/-.*?-/', '', open(f).read(), flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    for l in s.splitlines():
        if re.search(r'\b(sorry|admit|native_decide)\b', l) or re.search(r'(?<![\w.])axiom(?![\w.])', l):
            print(f"  {f}: {l.strip()}"); bad = 1
sys.exit(bad)
PY
echo "PASS: no sorry, admit, native_decide or axiom"

echo "=== 2. compile (project: $PROJ) ==="
cd "$PROJ" || exit 1
LP="$(lake env printenv LEAN_PATH)" || { echo "FAIL: lake env"; exit 1; }
for m in $MODULES; do
  t0=$(date +%s)
  LEAN_PATH="$OUT:$LP" lean --root="$HERE" -o "$OUT/TwoDicritical/$m.olean" "$HERE/TwoDicritical/$m.lean" \
    > "$OUT/$m.log" 2>&1
  rc=$?
  echo "TwoDicritical.$m: exit $rc, $(( $(date +%s) - t0 )) s"
  if [ $rc -ne 0 ] || grep -qE "error|declaration uses .sorry." "$OUT/$m.log"; then
    echo "FAIL: TwoDicritical.$m"; cat "$OUT/$m.log"; exit 1
  fi
done

echo "=== 3. axioms ==="
cat "$OUT/Axioms.log"
STD="(propext|Classical\.choice|Quot\.sound)"
n_all=$(grep -c "^#print axioms" "$HERE/TwoDicritical/Axioms.lean")
n_ok=$(grep -cE "depends on axioms: \[$STD(, $STD)*\][[:space:]]*$|does not depend on any axioms" "$OUT/Axioms.log")
if [ "$n_ok" -ne "$n_all" ]; then echo "FAIL: $n_ok of $n_all theorems on the standard axioms"; exit 1; fi
echo "PASS: $n_all of $n_all theorems on the standard axioms (or a subset)"
echo "=== TWO-DICRITICAL LEAN: ALL CHECKS PASSED ==="
