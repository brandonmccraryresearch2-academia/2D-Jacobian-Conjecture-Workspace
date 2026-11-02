#!/usr/bin/env bash
# check.sh -- Comparator-harness pin check for branch (c) grade A (prototype).
#
#   bash check.sh [SOLUTION.lean]
#
# Checks, in order:
#   1. PIN INTEGRITY: the statement of `challenge_interface` in Challenge.lean
#      agrees with `chartEmptyC_T1ne0_of_certificate` in ../lean/GradeA/Chart/
#      Assembly.lean, modulo whitespace and the theorem name.
#   2. CHALLENGE HYGIENE: Challenge.lean contains exactly two `sorry` (the two
#      theorem pins) and no `axiom`, `admit`, or `native_decide` (comments
#      stripped, as in ../build.sh).
#   3. SOLUTION SCAN (only if a file is given): the candidate solution contains
#      no `sorry`, `admit`, `axiom`, or `native_decide`.
# Kernel-level verification (compile + exported-statement comparison +
# `#print axioms` against the permitted list in comparator.json) is NOT done
# here; it requires the built branch-(c) overlay. See README.md.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
CHALLENGE="$HERE/Challenge.lean"
ASSEMBLY="$HERE/../lean/GradeA/Chart/Assembly.lean"
fail=0

strip_comments() { # strip /- -/ blocks (incl. /-- and /-! docstrings) and -- line comments
  awk '
    {
      line = $0; out = ""
      while (length(line) > 0) {
        if (inblock) {
          j = index(line, "-/")
          if (j == 0) { line = "" }
          else { line = substr(line, j + 2); inblock = 0 }
        } else {
          i = index(line, "/-")
          c = index(line, "--")
          if (c > 0 && (i == 0 || c < i)) { out = out substr(line, 1, c - 1); line = "" }
          else if (i > 0) { out = out substr(line, 1, i - 1); line = substr(line, i + 2); inblock = 1 }
          else { out = out line; line = "" }
        }
      }
      print out
    }' "$1"
}

# --- 1. pin integrity -------------------------------------------------------
extract_stmt() { # file, theorem-name
  awk -v name="$2" '
    $0 ~ ("^theorem " name) { on = 1 }
    on { print }
    on && /:= by/ { exit }
  ' "$1" | sed "s/^theorem $2/theorem PIN/" | tr -s ' \t\n' ' '
}
a="$(extract_stmt "$ASSEMBLY" 'chartEmptyC_T1ne0_of_certificate')"
b="$(extract_stmt "$CHALLENGE" 'challenge_interface')"
if [ -n "$a" ] && [ "$a" = "$b" ]; then
  echo "PASS pin integrity: challenge_interface == chartEmptyC_T1ne0_of_certificate (mod whitespace/name)"
else
  echo "FAIL pin integrity: challenge statement differs from Assembly.lean"
  fail=1
fi

# --- 2. challenge hygiene ---------------------------------------------------
body="$(strip_comments "$CHALLENGE")"
nsorry="$(printf '%s' "$body" | grep -o 'sorry' | wc -l)"
if [ "$nsorry" -eq 2 ]; then
  echo "PASS challenge hygiene: exactly 2 sorry (the two theorem pins)"
else
  echo "FAIL challenge hygiene: found $nsorry sorry, expected 2"
  fail=1
fi
if printf '%s' "$body" | grep -qE 'axiom|admit|native_decide'; then
  echo "FAIL challenge hygiene: axiom/admit/native_decide present"
  fail=1
else
  echo "PASS challenge hygiene: no axiom/admit/native_decide"
fi

# --- 3. optional solution scan ----------------------------------------------
if [ "${1:-}" != "" ]; then
  if strip_comments "$1" | grep -qE 'sorry|admit|axiom|native_decide'; then
    echo "FAIL solution scan: $1 contains sorry/admit/axiom/native_decide"
    fail=1
  else
    echo "PASS solution scan: $1 is clean of sorry/admit/axiom/native_decide"
  fi
fi

echo "permitted axioms (comparator.json): propext, Quot.sound, Classical.choice"
exit $fail
