# Branch (c) — Build Status

Source: v3.1 bundle (2026-09-29, 23:40 CDT), verified 23:28–23:36 CDT the same day.
Full record: `bundle_v3_1/jacobian_lean/BRANCH_C_LEAN_STATUS.md`; comprehensive guide: `GUIDE.md` §1.3, §13.

## Lean modules (all built, `verify_branch_c_lean.sh` passes, exit 0)

| Group | Modules | State |
|---|---|---|
| v1/v2 branch-(c) modules (`Degree19`, `LayerE2`, `LayersGen`, `Edge19`, `OmegaSquare`, `OmegaEdge`, `DescentClaim`, `Descent/**` (59), `Rank/**` (96)) | 162 | built in v2; axioms audited (`logs/axioms_branch_c.v2.log`) |
| `Descent2R/Facts`, `Vals_*`, layers L4, L3, L2c, L1, L0, Lm1, Lm2 | 505 | built (`logs/build_refl.log`: 2.9 h module time, peak 5.6 GB RSS) |
| `CondsC` | 1 | built (175 s, peak 1.78 GB) |
| `Descent2R/Main` (`chart_descent_refl`) | 1 | built: "Build completed successfully (1243 jobs)", 2,298 s, peak 3.34 GB |
| `Descent2R/Bridge` | 1 | built after a fix (269 s, no warnings) — a bug found and fixed after v3.0 |
| `T1Zero/Defs`, `Sq`, `F_*` (6), `P_*` (6), `Final` | 14 | built, 0 warnings (`P_*` 61–121 s, `Final` 46 s) |
| `T1Zero/Main` (`chartEmpty_t1_zero`) | 1 | built, 26 s |
| `T1Zero/Combine` | 1 | built, 22 s |
| Axiom audit (`AxiomsAuditBranchC.lean`) | 53 theorems | passed: 52 depend on `[propext, Classical.choice, Quot.sound]`; `Omega.omega_mod101_square` on `[propext, Quot.sound]` |
| `verify_branch_c_lean.sh` | — | passed, exit 0: prerequisite fingerprints; v2+v3 regeneration byte-identical; all 790 modules up to date; axioms; no `sorry`/`axiom`/`native_decide` |

## Outside Lean (grade B) — now corroboration (grade A since 2026-11-04)

*Note 2026-11-04.* The items below were the grade-B evidence for `ChartEmptyC`
until 2026-11-04, when `challenge_target` (`GradeA.Bridge`) proved
`ChartEmptyC_T1ne0` in Lean and `branch_c_eliminated` (`GradeA.Composition`)
eliminated branch (c). The grade is now A; the rank computation, the t₁ = 0
certificate, and the `rank_lemma_check/` premise checks stand as independent
corroboration (I1), not the sole support.

- `ChartEmptyC` (hence `ChartEmptyC_T1ne0`) via the rank lemma + full row rank of the
  W = 24 Macaulay matrix (3199 × 3199) mod p = 1000003 (w₀ = 806739) and mod p = 32003
  (w₀ = 11147): FLINT `nmod_mat.rank` and an independent numpy elimination agree;
  planted-zero control drops rank to 3198 as required. Script:
  `bundle_v3_1/jacobian_lean/chart_certificates/step3b_rank_lift.py` (6.5 min, 0.5 GB).
- t₁ = 0 slice: exact certificate over K₅ (degree 2, 75 K₅-terms), checked by an
  independent FLINT script; 5 negative controls fail as required.
- **Added 2026-10-06:** `rank_lemma_check/run.sh` passed (exit 0, `RESULT: PASS`, about 4.5 min on 2 cores).
  - R is irreducible over ℚ.
  - The generators of the rank computation equal the Lean conditions of `CondsC.lean` up to positive integer
    factors, exactly; two controls are rejected.
  - An explicit inverse of the W = 24 pivot block mod 32003 is checked by the Lean kernel.
    - 8 data modules and 8 check modules: 6398 theorems, every `#print axioms` giving `[propext]`.
    - About 7 CPU-minutes, at ≤ 1.8 GB per module.
    - Five controls are rejected.
    - The regenerated Lean files are byte-identical to `logs/MANIFEST.sha256`.
  - The grade is now A (since 2026-11-04). The kernel check covers the arithmetic, and the link to `ChartEmptyC_T1ne0` is in Lean (`challenge_target`, `GradeA.Bridge`).
- **Added 2026-10-06:** `muse_refutation/check_refutation.sh` passed. The clean copy of the refutation builds with
  exit 0, with no error and no warning, and its axioms are `[propext, reduction_lemma, Classical.choice,
  Quot.sound]`. The bundle copy reports one recovered error, an unknown `eval_one`, and exits 1.

## Provenance

- v3.1 supersedes v3.0 (bundled while the build was still running); §13 of GUIDE.md
  records what changed (the build, the fixed `Bridge` bug, the verification, verbose logs).
- The v2 corrected-commit proposal **was applied** to repo main as commit `2b77cd4`
  ("Branch (c): corrected elimination scripts", 2026-09-29).
  - Its `branch_c/` tree is byte-identical to `bundle_v3_1/v2_carryover/corrected_commit_proposal/proposed_branch_c/`.
  - The top-level `branch_c/` directory was later removed in `d65a007` (2026-10-01), so the corrected scripts are now
    in the git history and in `…/corrected_commit_proposal/final/`.
  - This was found and recorded on 2026-10-06.
  - The "not applied" lines in `GUIDE.md` and inside `bundle_v3_1/` predate this check. Those files are byte-for-byte
    copies of the v3.1 bundle and are left unchanged.
  - *Updated 2026-10-06.* Since then, `GUIDE.md` and `paper/BRANCH_C_GUIDE.md` are maintained copies, and their
    three "not applied" lines carry a correction. The copies inside `bundle_v3_1/` stay unchanged.
- This package itself pushed, published, uploaded, deposited and minted nothing.
- `CHECKSUMS.md5` and `CHECKSUMS.sha256` were regenerated on 2026-10-06, with the same rule: every committed file
  except the checksum files themselves, sorted by path.
  - Three entries had been stale since the 2026-10-01 Fira revision of the paper: `paper/README.md`,
    `paper/branch_c_elimination.tex` and `.pdf`.
  - The nine files in `paper/figures/` had never been listed.
  - The lists now have 1033 entries, and all of them verify.
  - *Regenerated again later on 2026-10-06*, with the same rule, after the additions (`rank_lemma_check/`,
    `muse_refutation/`) and the edits to `GUIDE.md`, `paper/BRANCH_C_GUIDE.md`, `README.md` and this file. The rule
    excludes every file named `CHECKSUMS.md5` or `CHECKSUMS.sha256`, including the two inside
    `bundle_v3_1/v2_carryover/`. The lists now have 1087 entries, and all of them verify.
  - *Regenerated on 2026-10-12*, with the same rule. PR #13 (2026-10-07) had added
    `correspondence_guide/CORRESPONDENCE_GUIDE.md` without a manifest entry; the guide's section mapping and
    `README.md` were corrected in the same change. The lists now have 1088 entries, and all of them verify.

## 2026-10-12: `grade_a/`, the generic half of `ChartEmptyC_T1ne0` in Lean

- New folder `grade_a/` (outside the bundle, which is unchanged): `R67Data`, `IrreducibleR`, `Transfer`, `Macaulay`,
  `Axioms`. Lean 4.34.0, Mathlib v4.34.0, no `sorry`, 12 theorems on the standard axioms (`grade_a/logs/build.log`,
  about 2 min on 2 cores, from scratch).
- R irreducible over ℚ (H3, C11) is now grade A (`Rrat_irreducible`).
- `no_common_zero_of_certificate`: a modular left inverse of a Macaulay block, at a root of R mod p, excludes common
  zeros of the generators at every root of R in every field of characteristic 0. The transfer goes through ℤ[X].
  What remains for `ChartEmptyC_T1ne0` is listed in `grade_a/README.md`: the six generators and the chart reduction,
  the rows and pivot columns, and the link from the packed kernel check to the Macaulay block (A1, A2). The grade
  of `ChartEmptyC_T1ne0` stays B.
- `CHECKSUMS.md5` / `CHECKSUMS.sha256` regenerated with the same rule.

## 2026-10-12 (evening): the chart reduction and the interface theorem

- `grade_a/certgen/gen_chart.py` computes the six chart generators with b₁₁,₂₀ free and their certificates from the
  bundle's own generator code (read-only), checks them by exact integer arithmetic, and checks that they are the
  rank check's generators up to one constant each (at p = 32003 and 1000003). `gen_chart_lean.py` writes
  `grade_a/lean/GradeA/Chart/{Gens,F_*,Main}.lean`.
- Kernel-checked (no `sorry`, standard axioms, 13 theorems; `grade_a/logs/build_chart.log`, about 4 min):
  - `chart_gens_vanish`: a chart point is a common zero of the six generators;
  - `denote_exprOfTerms_chartCtx`: the bridge to `MvPolynomial (Fin 5) ℤ[X]`;
  - `chartEmptyC_T1ne0_of_certificate`: `ChartEmptyC_T1ne0 L` for every field of characteristic 0, from the
    Macaulay data and the deliverables A1 and A2.
- What remains is listed in `grade_a/README.md`: the rows, pivot columns and support condition; A1; A2. The grade of
  `ChartEmptyC_T1ne0` stays B until they are supplied.
- `grade_a/build.sh` and `build_chart.sh` stop with exit status 2 when the given project lacks compiled Mathlib (or,
  for `build_chart.sh`, the built bundle), instead of letting `lake` start cloning it.
- `CHECKSUMS.md5` / `CHECKSUMS.sha256` regenerated with the same rule.

## 2026-10-13: an outside referee's caution for A2, and the source scan

- `grade_a/certgen/gen_chart.py` checks that the six generators are reduced modulo R: every w-exponent is below 5,
  and every coefficient is nonzero (check 5). This makes the ℤ[X]-support of each F_n equal to its K₅-support, which
  the support condition `hsupp` of A2 needs, since `build_matrix.py` builds the rows from K₅-supports. The caution is
  recorded in `grade_a/README.md`.
- `grade_a/build.sh` and `build_chart.sh`: the source scan catches the keyword `axiom` anywhere on a line
  (`noncomputable axiom`, `protected axiom`). Both were rerun: 12/12 and 13/13 theorems on the standard axioms
  (`grade_a/logs/build.log`, `logs/build_chart.log`).
- `CHECKSUMS.md5` / `CHECKSUMS.sha256` regenerated with the same rule.

## 2026-11-04–06: branch (c) eliminated in Lean; grade A

- A1 compiled 2026-10-31, A2 2026-11-01, `hsupp2` 2026-11-02; `challenge_target`
  + `branch_c_eliminated` proved 2026-11-04 on lean-build-2 (no hypotheses,
  permitted triple `[propext, Classical.choice, Quot.sound]`), re-verified
  2026-11-06 on lean-build-3; filed as tracked modules `GradeA.Bridge` /
  `GradeA.Composition` (commit `7e4db07f`). Status record:
  `grade_a/BRIDGE_STATUS_2026-11-06.md`. The "grade stays B" lines in the
  2026-10-12 sections above were true when written and are superseded by this
  section; they are retained as the dated record.
- The GGHV paper itself is now proved in full in Lean — CONDITIONAL, not
  unconditional — and filed (commit `484b5a8`, 2026-11-06;
  `gghv-dependency-closure/gghv_full_assembly_inventory.md`). The branch
  documents were combed to match (commit recorded in the comb report).
- `CHECKSUMS.md5` / `CHECKSUMS.sha256` regenerated 2026-11-07 with the same
  rule (every listed file re-hashed; the list composition is unchanged). The
  regeneration also repaired 32 entries that had gone stale since 2026-10-12
  (the 2026-11-04/06 addenda to `correspondence_guide/CORRESPONDENCE_GUIDE.md`
  and `grade_a/README.md`, `grade_a/build.sh`, `grade_a/lean/GradeA/Axioms.lean`,
  `paper/branch_c_elimination.pdf`, and 27 `rank_lemma_check/logs/` files).
  Note: `paper/README.md`'s md5 table for `branch_c_elimination.tex`/`.pdf`
  still records the pre-rebuild values and does not match the current files —
  flagged in the comb report, not changed here.
