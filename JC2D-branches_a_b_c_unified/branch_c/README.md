# Branch (c) Elimination — unified package

Elimination of GGHV normal form (1) [branch (c)] in the degree-(72,108) case of the
two-dimensional Jacobian conjecture.

This package follows the format of the branch-(a,b) elimination paper package
(`../branches_a_b/`, i.e. `branch_ab`, the v19 package) exactly, with the branch-(c) elimination
worked out **symbolically** (Lean 4 formalization) and **numerically** (exact and
modular certificates, finite-field rank computations).

## Format map (branch_ab [v19]  ->  branch (c))

| branch-(a,b) component | branch-(c) location | Notes |
|---|---|---|
| `paper/` (.tex/.pdf) | `paper/branch_c_elimination.tex` / `paper/branch_c_elimination.pdf` | The elimination paper (2026-09-30; 16 pages then, 18 pages in Fira since 2026-10-01), in the branch-(a,b) paper format; `paper/BRANCH_C_GUIDE.md` remains the comprehensive v3.1 reference. |
| `scripts/` | `bundle_v3_1/jacobian_lean/certgen_c/`, `bundle_v3_1/jacobian_lean/chart_certificates/`; since 2026-10-06 also `rank_lemma_check/` | Generators (exact, python-flint) and certificate/rank scripts. Kept inside `jacobian_lean/` because `verify_branch_c_lean.sh` requires `certgen_c/`, `chart_certificates/` and `Jacobian/` as siblings. `rank_lemma_check/` sits outside the bundle and only reads it. |
| `lean/` | `bundle_v3_1/jacobian_lean/Jacobian/BranchC/` | v1/v2 modules, `Descent2R` (505 generated modules), `T1Zero`, `Combine`, `Bridge`, `CondsC` |
| `audits/` | `bundle_v3_1/jacobian_lean/axioms_branch_c.log`, `bundle_v3_1/v2_carryover/branch_c_audit/` | Axiom audit (53 theorems) + v2 audit carryover |
| `correspondence_guide/` | `correspondence_guide/CORRESPONDENCE_GUIDE.md` | Created 2026-10-07 (PR #13); section mapping corrected 2026-10-12. Maps the paper's sections and the six statements to Lean names, files and grades. |
| `figures/` | `paper/figures/` | Four figures of the paper, with the scripts that render them (2026-10-01). |
| `logs/` | `bundle_v3_1/logs/` | Every build / verify / control / diagnostics log (index: GUIDE.md §9) |
| `BUILD_STATUS.md` | `BUILD_STATUS.md` | Full build and verification record |
| `CHECKSUMS.md5` / `CHECKSUMS.sha256` | `CHECKSUMS.md5` / `CHECKSUMS.sha256` | Generated over this `branch_c/` tree |
| `verify_v19.sh` | `verify_branch_c.sh` | Wrapper delegating to `bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh` |

## The v3.1 bundle, preserved intact

`bundle_v3_1/` is the reviewer's v3.1 bundle **byte-for-byte** (verified against its
`MANIFEST.sha256` at assembly time): the Lean overlay, all generators and data, every
log, the diagnostics, the `muse_refutation/` note, and the `v2_carryover/`. It is kept
intact because `verify_branch_c_lean.sh` depends on the internal relative layout
(`certgen_c/`, `chart_certificates/`, `Jacobian/` as siblings under `jacobian_lean/`).

## Additions outside the bundle (2026-10-06)

| Path | What |
|---|---|
| `rank_lemma_check/` | Checks of the rank lemma's instance (claim C5). (1) R is irreducible. (2) The generators equal the Lean conditions of `CondsC.lean`, exactly, up to positive integer factors. (3) An explicit inverse of the W = 24 pivot block mod 32003 is checked by the Lean kernel: 6398 identities, axioms `[propext]`, 5 controls. Also an I3 replication specification and `feasibility/`. `run.sh` takes about 4.5 min. C5 is grade A since 2026-11-04 (`challenge_target`); these checks stand as independent corroboration. |
| `muse_refutation/` | The Muse `char0_cert` bundle is withdrawn: its notice is `DEPRECATED_char0_cert.md`. A copy of the refutation builds cleanly; the bundle's copy reports one recovered error under Lean 4.34.0 and Mathlib v4.34.0. |
| `GUIDE.md`, `paper/BRANCH_C_GUIDE.md` | Now the maintained copies of the guide, updated on 2026-10-06 (their header lists the sections). `bundle_v3_1/GUIDE.md` keeps the v3.1 text. `README.txt` and `PARTS.txt` stay byte copies of the bundle's. |

The p-adic argument (`bundle_v3_1/jacobian_lean/chart_certificates/padic_DEFERRED/`) is closed as not needed. It is
an independent alternative, unreviewed and unused; see `GUIDE.md` §4.4.

## Verdict (v3.1, 2026-09-29)

- In Lean (no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`):
  `ChartEmptyC_T1ne0 → ChartEmptyC → DescentClaimC → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P,Q] = λx²`.
  The stratum b_{11,20} = 0 is kernel-checked (`T1Zero`); `Combine` isolates
  the chart-emptiness premise, now itself proved in Lean.
- Since 2026-11-04, `ChartEmptyC_T1ne0` itself is proved in Lean
  (`challenge_target`, `GradeA.Bridge`; `branch_c_eliminated`,
  `GradeA.Composition`): the rank lemma plus full row rank of the W = 24
  Macaulay matrix mod 1000003 and mod 32003 (two implementations, controls)
  now stand as independent corroboration, as do the premise checks of
  `rank_lemma_check/` and the kernel check of the arithmetic. The grade is A.
- Branch (c) is therefore **eliminated in Lean** (2026-11-04). Together with
  the branches (a),(b) `main_theorem`, the GGHV Prop. 4.3 case (8,28) split is
  fully eliminated in Lean. This does not claim (72,108) excluded
  unconditionally or JC(2). See `GUIDE.md` §1 for the full verdict.

## Reproduction

```bash
cd branch_c
bash verify_branch_c.sh   # delegates to bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh
bash rank_lemma_check/run.sh              # 2026-10-06: about 4.5 min; core Lean 4.34.0 only, python-flint, numpy
bash muse_refutation/check_refutation.sh  # 2026-10-06: needs Mathlib v4.34.0 (e.g. ../branches_a_b/lean)
```

Requirements: elan/lake (Lean 4.34.0, Mathlib v4.34.0), python3 with python-flint and sympy.
Single modules peak at ~5.6 GB RSS; allow 12+ GB or set LOWMEM=1.

## Scope

Not the Jacobian conjecture, not any other case of GGHV Prop. 4.3, not the reduction
from the conjecture to Prop. 4.3. Nothing here has been published, uploaded, deposited
or minted.
