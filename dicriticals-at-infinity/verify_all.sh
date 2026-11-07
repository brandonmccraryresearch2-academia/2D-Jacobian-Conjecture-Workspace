#!/bin/bash
# verify_all.sh -- Re-run every script, check its exit code, and compare its output byte for byte with
# outputs/<name>.out.
# Two-Dicritical Line Closure, October 1, 2026.
# Revised 2026-10-12: the interpreter is $PYTHON (default python3; it was ~/miniconda3/envs/physics/bin/python,
# which exists on one machine only), and the outputs are now compared with the recorded ones (all 18 identical with
# Python 3.11.15 and sympy 1.14.0 on 2026-10-12). Passing shows that the computations reproduce. It does not show
# that the paper's main theorem is proved: see README.md, "Status".
set -u
PY="${PYTHON:-python3}"
DIR="$(cd "$(dirname "$0")" && pwd)"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
PASS=0
FAIL=0
for f in "$DIR"/scripts/*.py; do
    base=$(basename "$f" .py)
    if timeout 300 "$PY" "$f" > "$TMP/$base.out" 2>&1; then
        if cmp -s "$TMP/$base.out" "$DIR/outputs/$base.out"; then
            echo "PASS: $base"
            PASS=$((PASS+1))
        else
            echo "FAIL: $base (output differs from outputs/$base.out)"
            FAIL=$((FAIL+1))
        fi
    else
        echo "FAIL: $base (exit $?)"
        FAIL=$((FAIL+1))
    fi
done
echo "=== $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]
