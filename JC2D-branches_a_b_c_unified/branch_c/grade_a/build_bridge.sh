#!/usr/bin/env bash
# build_bridge.sh -- the Fpoly=Fpoly2 bridge + branch-(c) elimination as tracked
# modules (Lean 4.34.0, Mathlib v4.34.0).
#
# Usage: build_bridge.sh [BUNDLE_PROJECT]
#   BUNDLE_PROJECT is a Lake project in which the branch-(c) bundle is built,
#   i.e. which has the compiled modules Jacobian.BranchC.T1Zero.Combine
#   (default ../bundle_v3_1/jacobian_lean, after its own build). On lean-build-3
#   pass ~/tooling/work/overlay_c. Nothing is written into it: the .olean files
#   go to a temporary directory.
#
# Steps:
#   0. copy the filed tree oleans into a temporary directory (lean/GradeA/*,
#      lean/GradeA/Chart/*, and the rank-check top-level modules RCData00-07,
#      RCCommon, RCCheck00-07 from ../rank_lemma_check/lean/), and compile the
#      Chart modules not present as oleans (F_Psi, F_Phi1, F_Phi2, F_Theta1,
#      F_Theta2, F_Theta3, Main, Assembly) into it;
#   1. scan lean/GradeA/Bridge.lean and lean/GradeA/Composition.lean (comments
#      stripped) for sorry, admit, native_decide and the keyword `axiom`
#      anywhere on a line;
#   2. compile GradeA.Bridge, then GradeA.Composition, each with `lean -o`;
#      any error or "declaration uses sorry" fails;
#   3. check that every `#print axioms` line of the two modules names only
#      propext, Classical.choice, Quot.sound (or a subset).
# Exit status 0 iff all steps pass; 2 if the project lacks the compiled bundle
# or Mathlib (checked first). The dependency oleans copied in step 0 are the
# filed tree artifacts (built from the filed sources 2026-11-04/05; the 8
# grade-A modules were rebuilt from source by build.sh on 2026-11-05); only
# the Chart modules and the two new modules are compiled fresh here. Trusting
# prebuilt dependency oleans (Mathlib, the bundle) is the established
# convention; the filed GradeA oleans are additionally trusted here, having
# been rebuilt from source by build.sh on 2026-11-05.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
PROJ="${1:-$HERE/../bundle_v3_1/jacobian_lean}"
PROJ="$(cd "$PROJ" && pwd)" || { echo "FAIL: no Lean project at $PROJ"; exit 1; }
for f in .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean \
         .lake/build/lib/lean/Jacobian/BranchC/T1Zero/Combine.olean; do
  if [ ! -f "$PROJ/$f" ]; then
    echo "FAIL: $PROJ has no $f."
    echo "      Pass a Lake project in which the branch-(c) bundle is built (Mathlib v4.34.0 included)."
    exit 2
  fi
done
export PATH="$HOME/toolchain/bin:$HOME/.elan/bin:$PATH"  # lean-build-3: lake/lean live in ~/toolchain/bin, not ~/.elan/bin
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
mkdir -p "$OUT/GradeA/Chart"
RANKLEAN="$HERE/../rank_lemma_check/lean"

echo "=== 0. stage filed oleans, compile Chart modules ==="
cp "$HERE"/lean/GradeA/*.olean "$OUT/GradeA/"
cp "$HERE"/lean/GradeA/*.olean "$OUT/"
cp "$HERE"/lean/GradeA/Chart/*.olean "$OUT/GradeA/Chart/"
cp "$RANKLEAN"/*.olean "$OUT/"
echo "staged: $(ls "$OUT"/GradeA/*.olean | wc -l) GradeA oleans, $(ls "$OUT"/RC*.olean | wc -l) rank-check oleans"
cd "$PROJ" || exit 1
LP="$(lake env printenv LEAN_PATH)" || { echo "FAIL: lake env"; exit 1; }
compile_chart() {  # $1 = module path relative to GradeA, $2 = label
  local t0=$(date +%s)
  LEAN_PATH="$OUT:$LP" lean --root="$HERE/lean" -o "$OUT/GradeA/$1.olean" "$HERE/lean/GradeA/$1.lean" \
    > "$OUT/$2.log" 2>&1
  local rc=$?
  echo "GradeA.$2: exit $rc, $(( $(date +%s) - t0 )) s"
  if [ $rc -ne 0 ] || grep -qE "error|declaration uses .sorry." "$OUT/$2.log"; then
    echo "FAIL: GradeA.$2"; tail -40 "$OUT/$2.log"; exit 1
  fi
}
for m in F_Psi F_Phi1 F_Phi2 F_Theta1 F_Theta2 F_Theta3 Main Assembly; do
  compile_chart "Chart/$m" "Chart.$m"
done

echo "=== 1. source scan ==="
python3 - "$HERE"/lean/GradeA/Bridge.lean "$HERE"/lean/GradeA/Composition.lean <<'PY' || { echo "FAIL: sorry/admit/native_decide/axiom found"; exit 1; }
import re, sys
bad = 0
for f in sys.argv[1:]:
    s = re.sub(r'/-.*?-/', '', open(f).read(), flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    for l in s.splitlines():
        if re.search(r'\b(sorry|admit|native_decide)\b', l) or re.search(r'(?<![\w.])axiom(?![\w.])', l):
            print(f"  {f}: {l.strip()[:120]}"); bad = 1
sys.exit(bad)
PY
echo "PASS: no sorry, admit, native_decide or axiom"

echo "=== 2. compile the bridge and composition modules ==="
compile() {  # $1 = module name (Bridge|Composition)
  local t0=$(date +%s)
  LEAN_PATH="$OUT:$LP" lean --root="$HERE/lean" -o "$OUT/GradeA/$1.olean" "$HERE/lean/GradeA/$1.lean" \
    > "$OUT/$1.log" 2>&1
  local rc=$?
  echo "GradeA.$1: exit $rc, $(( $(date +%s) - t0 )) s"
  if [ $rc -ne 0 ] || grep -qE "error|declaration uses .sorry." "$OUT/$1.log"; then
    echo "FAIL: GradeA.$1"; tail -40 "$OUT/$1.log"; exit 1
  fi
}
compile Bridge
compile Composition

echo "=== 3. axioms ==="
cat "$OUT/Bridge.log" "$OUT/Composition.log"
STD="(propext|Classical\.choice|Quot\.sound)"
n_all=$(cat "$HERE"/lean/GradeA/Bridge.lean "$HERE"/lean/GradeA/Composition.lean | grep -c "^#print axioms")
n_ok=$(cat "$OUT/Bridge.log" "$OUT/Composition.log" | grep -cE "depends on axioms: \[$STD(, $STD)*\][[:space:]]*$|does not depend on any axioms")
if [ "$n_ok" -ne "$n_all" ]; then echo "FAIL: $n_ok of $n_all theorems on the standard axioms"; exit 1; fi
echo "PASS: $n_all of $n_all theorems on the standard axioms (or a subset)"
echo "=== BRIDGE + BRANCH-(c) ELIMINATION: ALL CHECKS PASSED ==="
