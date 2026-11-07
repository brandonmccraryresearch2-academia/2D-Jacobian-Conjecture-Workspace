# Grade-A status — 2026-11-05 (repair leg; supersedes GRADE_A_STATUS_2026-11-04.md)

**Update 2026-11-06.** The "Scope guard" below says the bridge/composition files
(`challenge_target`, `branch_c_eliminated`) "remain scratch, not repo-tracked
modules" — that was true on 2026-11-05 and is superseded: they are now filed as
tracked modules `GradeA.Bridge` / `GradeA.Composition` (commit `7e4db07f`,
2026-11-06; status record `BRIDGE_STATUS_2026-11-06.md`). The body of this
file is retained as the 2026-11-05 record, not rewritten.

**This tree is green: the full `gradea_build` passes end to end.**
Validated by deepest-research fact-check, 2026-11-05:
`~/workspace/research/tooling/gradea_validation_2026-11-05.md` (GO).

## What passed (lean-build-3, Lean 4.34.0 / Mathlib v4.34.0)

- Full `gradea_build`: all 8 modules exit 0 — R67Data (12 s), R109Data
  (295 s), IrreducibleR (5 s), IrreducibleR109 (6 s), K5Field (4 s),
  Transfer (4 s), Macaulay (5 s), Axioms (3 s) — plus the `#print axioms`
  check: 22 of 22 theorems on the standard axioms (or a subset),
  `sorryAx` absent.
- Log: `~/workspace/research/tooling/logs_gcp_phase3/logs/gradea_build_2026-11-04_leg2b.log`
  (workspace copy; not committed here).

## What was repaired (vs the leg-1 failure)

- `IrreducibleR109.lean`: all 13 leg-1 errors fixed as Mathlib v4.34.0 API
  adaptations — `Polynomial.mod_add_div` → `EuclideanDomain.div_add_mod'`,
  `coeff_natDegree` / `as_sum_range_C_mul_X_pow` used as the equations they
  are (`as_sum_range_C_mul_X_pow'`), `hr.of_dvd` → `isRoot_of_dvd` (the
  old name resolved to the nonexistent `Eq.of_dvd`), `reduceMod109`
  marked `noncomputable`, `Ideal.Quotient.lift` given a genuine ring hom
  (`(Ideal.Quotient.mk _).comp reduceMod109`), `Polynomial.coe_mapRingHom`,
  `set_option maxRecDepth` 10000 / 100000 where the kernel demanded it.
  No public theorem statement changed; the only name change is the helper
  lemma `IsRoot.of_dvd` → `isRoot_of_dvd`.
- `K5Field.lean`: latent errors found by the intermediate leg-2 run and
  fixed — `example : Field K5` marked `noncomputable`, ambiguous `gcd`
  qualified to `EuclideanDomain.gcd` (the unqualified spelling was
  ambiguous between `EuclideanDomain.gcd` and `GCDMonoid.gcd`).
  No public theorem statement changed (same propositions, qualified spelling).
- `R109Data.lean`: the renamed port (`Rint109` internal; downstream
  statements `bezout_lin`, `bezout_quad_small`, `quad_mod` unchanged —
  `quad_mod` carries type ascriptions on `X` only).
- `Axioms.lean`: imports added for `GradeA.IrreducibleR109` and
  `GradeA.K5Field` (the B2 fix); no `#print axioms` line changed.

## Scope guard

Green means the eight grade-A modules compile and their 22 audited theorems
sit on the standard axioms (or a subset). It does NOT claim (72,108)
excluded unconditionally and does NOT prove JC(2): those still rest on GGHV
exhaustiveness + the reduction chain, ledgered, not re-derived. The
bridge/composition files (`challenge_target`, `branch_c_eliminated`) remain
scratch, not repo-tracked modules.

## Superseded note

`GRADE_A_STATUS_2026-11-04_SUPERSEDED.md` (the 2026-11-04 note, NOT green)
is retained alongside this file for the record; its claims were true at the
time and are superseded by the run above, not edited away.
