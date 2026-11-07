#!/bin/bash
# Leg G runner driver 2 — CORRECTED Singular invocation.
# Driver 1 used `Singular < script < /dev/null`: the second redirect wins,
# so Singular read empty stdin and never executed the scripts (banner-only
# logs, rc=0 — VOID runs). Correct form: `Singular < script` (stdin = the
# script file; each script ends with quit;). timeout 600 guards a hang.
# No script file was modified; only the invocation changed. Logged verbatim.
cd /tmp/legG || exit 99
fail=0
run() { # $1 = log name, $2 = script
  local log="$1"; local scr="$2"
  echo "--- START $log : $(date -u +%FT%TZ) ---"
  timeout 600 Singular < "$scr" > "logs/$log" 2>&1
  local rc=$?
  echo "--- END $log : rc=$rc ---"
  if [ "$rc" -ne 0 ]; then fail=$((fail+1)); fi
}
run e13_singular.log gghv_full_singular_e13_ode_2026-11-06.sing
run table_s5_singular.log gghv_full_singular_table_s5_2026-11-06.sing
run ggv5_families_singular.log gghv_full_singular_ggv5_families_2026-11-06.sing
run nine_eq_singular.log gghv_full_singular_nine_eq_2026-11-06.sing
echo "DRIVER2_FAIL_COUNT=$fail"
exit "$fail"
