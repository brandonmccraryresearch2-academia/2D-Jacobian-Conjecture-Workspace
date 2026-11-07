#!/bin/bash
# Leg G runner driver — runs all 7 scripts + filed cross-check on lean-build-3.
# Logs to /tmp/legG/logs/. Exit code = number of failed runs (0 = all ok).
cd /tmp/legG || exit 99
mkdir -p logs
PY="$HOME/miniconda3/envs/jacobian-conjecture-2d/bin/python3"
if [ ! -x "$PY" ]; then PY="python3"; fi
echo "PY=$PY"
which Singular; which "$PY"
fail=0
run() { # $1 = log name, $2.. = command
  local log="$1"; shift
  echo "--- START $log : $(date -u +%FT%TZ) ---"
  "$@" > "logs/$log" 2>&1
  local rc=$?
  echo "--- END $log : rc=$rc ---"
  if [ "$rc" -ne 0 ]; then fail=$((fail+1)); fi
}
{
  echo "=== tool versions ==="
  Singular --version < /dev/null
  "$PY" -c "import sys, sympy, flint; print(sys.version); print('sympy', sympy.__version__); print('flint', flint.__version__)"
} > logs/versions.log 2>&1
echo "versions rc=$?"
run e13_singular.log Singular < gghv_full_singular_e13_ode_2026-11-06.sing < /dev/null
run e13_sympy.log "$PY" gghv_full_singular_e13_sympy_2026-11-06.py
run table_s5_singular.log Singular < gghv_full_singular_table_s5_2026-11-06.sing < /dev/null
run ggv5_families_singular.log Singular < gghv_full_singular_ggv5_families_2026-11-06.sing < /dev/null
run ggv5_families_py.log "$PY" gghv_full_singular_ggv5_families_py_2026-11-06.py
run nine_eq_singular.log Singular < gghv_full_singular_nine_eq_2026-11-06.sing < /dev/null
run nine_eq_sympy.log "$PY" gghv_full_singular_nine_eq_sympy_2026-11-06.py
run table_filed_py.log "$PY" d1_singular_table_enum_2026-11-05.py
echo "DRIVER_FAIL_COUNT=$fail"
exit "$fail"
