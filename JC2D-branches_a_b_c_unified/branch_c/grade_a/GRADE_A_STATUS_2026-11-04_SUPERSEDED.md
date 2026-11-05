# Grade-A status — 2026-11-04 (LEG 1 + LEG 4 record)

**This tree is NOT green. Do not describe the grade-A package as passing.**

## What passed, standalone (LEG 1, lean-build-3)

- R109Data (renamed R109 port): PASSED its fresh foreground re-check
  (`LEAN_EXIT=0`). The earlier 22:58 CST aborted check's orphan was killed
  and its verdict was unobservable; the fresh run replaces it.
- Log: `~/workspace/research/tooling/logs_gcp_phase3/logs/r109_port_recheck_2026-11-04_foreground.log`
  (workspace copy; not committed here).

## What failed (LEG 1, full `gradea_build`, same run)

- R67Data: PASS.
- R109Data: PASS (393 s).
- IrreducibleR: PASS.
- **IrreducibleR109: FAIL (exit 1, 13 error lines)** — Mathlib v4.34.0
  API drift in `IrreducibleR109.lean` itself, e.g. unknown constant
  `Polynomial.mod_add_div`, `coeff_natDegree` /
  `as_sum_range_C_mul_X_pow` used as functions, `hr.of_dvd` invalid
  field, `reduceMod109` missing `noncomputable`, an
  `Ideal.Quotient.lift` composition issue.
- **NONE of the 13 errors is in the R109 port.**
- K5Field, Transfer, Macaulay, Axioms + the `#print axioms` check were
  NOT RUN (fail-fast).
- Full log: `~/workspace/research/tooling/logs_gcp_phase3/logs/gradea_build_2026-11-04_leg1_r109.log`
  (workspace copy; not committed here).

## Working-tree state (LEG 4, 2026-11-04)

Three files are modified in the working tree and were deliberately LEFT
UNCOMMITTED, so that no commit in this tree can be read as a passing
grade-A change:

- `lean/GradeA/Axioms.lean`
- `lean/GradeA/IrreducibleR109.lean`
- `lean/GradeA/R109Data.lean`

The IrreducibleR109 repair is a later leg's job, not LEG 4's. Once that
repair lands and a full `gradea_build` passes end to end (including
K5Field, Transfer, Macaulay, Axioms and the `#print axioms` check), this
note must be superseded by a new status note recording the green run —
not edited in place to claim green.
