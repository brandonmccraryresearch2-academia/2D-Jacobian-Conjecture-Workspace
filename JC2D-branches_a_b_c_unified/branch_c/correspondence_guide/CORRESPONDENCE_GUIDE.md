# Correspondence Guide: Branch (c) Elimination

This guide maps each proof element in the branch-(c) paper to its Lean 4
formalization and computational verification scripts. It follows the format of
`branches_a_b/correspondence_guide/CORRESPONDENCE_GUIDE.md`.

**Source freeze.** All Lean sources below live in the frozen v3.1 bundle:
`JC2D-branches_a_b_c_unified/branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/`.
The bundle is byte-identical to the v3.1 release (manifest verifies); cite it,
not working copies.

**Paper.** `JC2D-branches_a_b_c_unified/branch_c/paper/branch_c_elimination.pdf`
(18 pp, 2026-10-01).

## Paper Structure → Lean → Scripts

### Introduction, Main result, Logical status (§1)
- **Lean**: `main_theorem_c_of_chartEmpty_T1ne0` in `T1Zero/Combine.lean`
- **Statement**: `ChartEmptyC_T1ne0 L → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P,Q] = λx²`, over any characteristic-zero field L, with no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Logical status**: Branch (c) is closed **under the computational premises of the paper's §10** (`branch_c/GUIDE.md` §5.9; grade B, outside Lean). Not closed by Lean alone.

### Addendum 2026-11-04 — branch (c) eliminated unconditionally in Lean

The "not closed by Lean alone" statement above is superseded. On 2026-11-04,
branch (c) was eliminated unconditionally in Lean: `branch_c_eliminated`
(`gghv-dependency-closure/lean/composition_2026-11-04.lean`, 18 lines, no
hypotheses, axioms exactly `[propext, Classical.choice, Quot.sound]`) states
that no Keller pair with Newton normal form (c) exists over any field of
characteristic 0. It is `main_theorem_c_of_chartEmpty_T1ne0` (bundle
`Combine`) applied to `challenge_target`
(`gghv-dependency-closure/lean/bridge_attempt_2026_11_04.lean`, 54 lines), the
certificate interface instantiated at the concrete data ρ = Fin 3199,
p = 32003, w₀ = 11147, via the bridge `Fpoly = Fpoly2` (the same six
`polyOfTerms` generators in the same order: 0 = Psi, 1 = Phi1, 2 = Phi2,
3 = Theta1, 4 = Theta2, 5 = Theta3) and the A1, A2, and six data hypotheses;
R109Data and K5 were not needed. Verification logs:
`gghv-dependency-closure/lean/logs/bridge_challenge_target_2026-11-04.log`
and `gghv-dependency-closure/lean/logs/branch_c_eliminated_2026-11-04.log`.
These two files sit outside the frozen v3.1 bundle; the source freeze above
is unchanged. This eliminates GGHV Proposition 4.3 case (1) (with the
(0, 8)/(0, 12) vertices); together with the branches (a),(b) `main_theorem`
(case (2)), the Prop. 4.3 split is fully eliminated in Lean. It does not
claim (72, 108) excluded unconditionally or JC(2).

### Addendum 2026-11-06 — the bridge and composition as tracked modules

The two leg files above are now also filed as tracked Lean modules in the
tree, alongside grade A: `grade_a/lean/GradeA/Bridge.lean` (module
`GradeA.Bridge`: `bridge_Fpoly`, `hsupp_chart`, `hA2_chart`,
`challenge_target`) and `grade_a/lean/GradeA/Composition.lean` (module
`GradeA.Composition`: `branch_c_eliminated`), compiled and audited by
`grade_a/build_bridge.sh` (stages the filed oleans, fresh-compiles the eight
chart modules, scans, compiles the two modules, audits the `#print axioms`
lines; default bundle project `../bundle_v3_1/jacobian_lean`). The module
theorems are byte-identical to the 2026-11-04 scratch proofs; only the
headers changed, plus one import line (`import bridge_attempt_2026_11_04` →
`import GradeA.Bridge`). Re-verified 2026-11-06 on lean-build-3 (Lean 4.34.0):
baseline parent re-check of the scratch-identical copies plus
`build_bridge.sh` against the actual module files — all modules exit 0, both
theorems on the permitted triple `[propext, Classical.choice, Quot.sound]`.
Status record: `grade_a/BRIDGE_STATUS_2026-11-06.md`. The leg files at
`gghv-dependency-closure/lean/` stay in place as the filed record, and the
frozen bundle is untouched.

### Source data (§2)
- **Source-gating**: All base objects verified against GGHV v1, Proposition 4.3, case (1). The pipeline's generators were found to certify a differently parametrized ideal than `lower_c`'s; step 1 was redone for `lower_c` (`chart_certificates/step1/`, `logs/run_step1.log`).
- **Step-1 scripts** (`chart_certificates/step1/`): `certB_lowerc.py` (exact over K₅, t₁ = 0 slice), `modp_chart.py`
  (𝔽₁₀₁, 𝔽₁₀₀₀₀₀₃, 𝔽_{109⁵}); checkers `check_certB_lowerc.py` (independent FLINT substitution) and
  `check_modp_chart.py` (random evaluation). Controls: perturbed coefficient, Θ₃ dropped, wrong w — all rejected.
  (Version 1 of this guide listed these under §3.)

*Section mapping corrected 2026-10-12.* Version 1 of this guide (PR #13) attached the Lean objects of §§4–8 to the
wrong sections: it put the descent (`chart_descent_refl`, the paper's B5) under §4, the 132-equation bridge (B4)
under §5, and `CondsC.lean` under §6, and it listed §1–§2 chart scripts under §3. The mapping below follows the
paper's own labels B0–B8 (its §11 table) and was checked against `branch_c_elimination.tex`.

### The polynomial system (§3)
- **Lean**: the supports `rangeP`, `rangeQ` and the hypothesis `NewtonNFc` (`DescentClaim.lean`); the layer identity
  `EIdent` (`LayersGen.lean`); the lattice counts 61 and 125 and the ten vertices (`latticeNPc_card`,
  `latticeNQc_card`, `verticesc_mem` in `Degree19.lean`).
- **Scripts**: `branch_c_stage1_setup.py` (supports, lattice counts, layers), kept in
  `bundle_v3_1/v2_carryover/corrected_commit_proposal/` (versions `orig/`, `fixed/`, `final/`, with logs).

### Exact layer reduction (§4): B0 and B4
- **B0 (Lean, v1)**: `layers_of_jac_c`, `layer_bracket_gen` (`LayersGen.lean`): from `jac P Q = C λ · x²` and
  `NewtonNFc`, the identities `EIdent A B λ n` for every layer n ≥ −20.
- **B4 (Lean, v3)**: `coeff_layerTermZ`, 179 zero facts from `rangeP`/`rangeQ`, and the 132 raw equations by
  `linear_combination` (`Descent2R/Bridge.lean`, generated by `certgen_c/gen_bridge_c.py`).
- **Grade**: A.

### Normalization (§5): B1, B2 and B3
- **B1 (Lean, v1)**: the top layer n = 5 is the branch-(a,b) problem: `eIdent_five`, and the branch-(a,b)
  classification `topLayerClassification_of_chart (chartClassification_holds L)`, used inside
  `main_theorem_c_of_claim`. These two theorems live in the branch-(a,b) Lean project
  (`branches_a_b/lean/Jacobian/BranchAbChart.lean`, line 125; `ChartProof/Final.lean`, line 32), which the branch-(c)
  build requires underneath.
- **B2 (Lean, v1/v2)**: degree-19 rigidity, b₁₂,₂₄ ≠ 0 ⇒ t₂ = b₁₂,₂₂ ≠ 0: `degree19_rigidity`, `t0_vertex_rigidity`
  (`Degree19.lean`), `t0_vertex_rigidity_of_jac` (`LayerE2.lean`), `edge19_rigidity_of_jac`,
  `vertex_12_24_forces_t2` (`Edge19.lean`). Control: `degree19_bound_sharp` (the degree bound is sharp).
- **B3 (Lean, v1)**: torus and weighted scaling to the rescaled K₅ top layer and the chart b₁₂,₂₂ = 1:
  `eIdent_transport`, `main_theorem_c_of_claim` (`DescentClaim.lean`). Its output is the hypotheses of
  `DescentClaimC`: the 19 top-layer values, the 123 unknowns, the 132 raw equations.
- **Grade**: A. `#print axioms` gives the three standard axioms for `degree19_rigidity`, `vertex_12_24_forces_t2`
  and `main_theorem_c_of_chartEmpty_T1ne0` (`bundle_v3_1/logs/verify_v3.log`).

### The top layer (§6)
- **Lean**: no new module. The n = 5 layer is inherited from branch (a,b) (B1); the 19 top-layer values enter
  `Descent2R/Main.lean` as the hypothesis `h_v`.
- **Discrepancy in the paper (found 2026-10-12, not yet corrected in the paper).** The paragraph "Formalization
  seam" of §6 says that the degree-19 rigidity lemma is *not* formalized inside Lean, that the classification
  ruling out deg f > 19 is supplied by the external certified point `e5_cert.json`, and that this step is grade B.
  The frozen bundle contradicts it:
  - `degree19_rigidity`, `vertex_12_24_forces_t2` and `edge19_rigidity_of_jac` are Lean theorems, with no `sorry`
    and the three standard axioms;
  - `main_theorem_c_of_claim` uses `vertex_12_24_forces_t2` and the Lean classification
    `chartClassification_holds` directly (`DescentClaim.lean`: the theorem at line 149, the two uses at lines 165
    and 169), and
    `main_theorem_c_of_chartEmpty_T1ne0` is `main_theorem_c_of_claim` applied to the chart statement
    (`T1Zero/Combine.lean`, line 55);
  - no branch-(c) Lean file mentions `e5_cert.json`.

  The paper's own §5 (B2) and its §11 table (B1–B3, grade A) agree with the Lean files. The "seam" paragraph refers
  to an audit of 2026-09-26, the day before the branch-(a,b) top-layer classification was completed in Lean (v17,
  `ChartProof`, 2026-09-27); it appears to be out of date. Until the paper is corrected, the Lean files decide: B1–B3
  are grade A, and the only step outside Lean is `ChartEmptyC_T1ne0` (§10).

### Descent (§7): B5
- **Lean**: `Descent2R/` — `L4` (54 modules), `L3` (57), `L2c` (57), `L1` (60), `L0` (60), `Lm1` (99), `Lm2` (110),
  plus `Facts`, `Vals_*`, `Main`, `Bridge` (9). Generated by `certgen_c/gen_refl_c.py` (chain) and
  `certgen_c/gen_bridge_c.py` (Bridge); every identity pre-checked in Python by exact integer arithmetic.
- **Main theorem**: `chart_descent_refl` in `Descent2R/Main.lean` — 752 `have`s, 231 via `cancel_int`; hypotheses
  `w` with R(w) = 0, the 19 top-layer K₅ values, the 123 unknowns, the 132 raw equations; conclusion the twelve
  conjuncts `cond_Omega w … = 0 ∧ … ∧ cond_Em2pure_17_37 w … = 0`.
- **The implication** `DescentClaimC ⇐ ChartEmptyC`: `descentClaimC_of_chartEmpty` (`Descent2R/Bridge.lean`).
- **Grade**: A (kernel reflection; built; axioms audited).

### The chart conditions (§8)
- **Lean**: the twelve conditions `cond_Omega … cond_Em2pure_17_37` (`CondsC.lean`, generated by
  `certgen_c/gen_conds_c.py`); the statement `ChartEmptyC` (`Descent2R/Bridge.lean`): the twelve conditions have no
  common zero with R(w) = 0 and b₁₂,₂₂ = 1.
- **The Ω parabola (§8.3)**: o₂² = 4o₁o₃ is checked in `chart_certificates/step1/lowerc_chart.py` and in
  `step3c_chart_identity.py`; o₁(w) ≠ 0 is proved in the Lean kernel by a Bezout identity (`T1Zero.s_X2`).

### The stratum b₁₁,₂₀ = 0 (§9): B7
- **Lean**: `chartEmpty_t1_zero` in `T1Zero/Main.lean` — kernel-checked.
- **Certificate**: `chart_certificates/step1/certB_lowerc.json` (degree 2, 75 K₅-terms), produced by
  `certB_lowerc.py` and rechecked by `check_certB_lowerc.py`.
- **Negative controls**: `diag/t1z_controls.py` → `logs/t1z_controls.log`: 5 controls (C1–C5) all **fail as required**.
- **Grade**: A.

### The whole chart (§10)
- **Proved in Lean (grade A, since 2026-11-04)**: the rank lemma + exact finite-field ranks at two primes (1000003, 32003), two implementations (FLINT `nmod_mat`, numpy elimination), exact input checks — `chart_certificates/step3b_rank_lift.py`, `step3b_rank_lift.log` — now stand as independent corroboration of `challenge_target` (`GradeA.Bridge`), which proves `ChartEmptyC_T1ne0` at the concrete data.
- **Rank-lemma premises (`GUIDE.md` §5.9)** → `branch_c/rank_lemma_check/`: 6398 packed natural-number identities (`C·M_S ≡ I` mod 32003 for the W = 24 pivot block), kernel-checked with axioms `[propext]` only; 5 negative controls rejected, 1 pass control accepted; generators matched exactly to the Lean `cond_*` (parsed from `CondsC.lean`); R irreducible (FLINT + mod-67 + degree patterns).
- **What Lean now checks**: the link from the pivot-block arithmetic to `ChartEmptyC_T1ne0` (plan A1–A5, done 2026-10-31–11-04; see the addenda above).

### Proof of the main theorem (§11)
- **Lean**: `T1Zero/Combine.lean` —
  - `chartEmptyC_of_T1ne0`: `ChartEmptyC_T1ne0 L → ChartEmptyC L`
  - `descentClaimC_of_chartEmpty_T1ne0`
  - `main_theorem_c_of_chartEmpty_T1ne0`: the top-level theorem.
- **Grade**: A for the implications; the premise `ChartEmptyC_T1ne0` is now
  itself proved in Lean (`challenge_target`, 2026-11-04), so the main theorem
  holds unconditionally as `branch_c_eliminated` (no hypotheses, standard
  axioms).

### Epistemic status (§12)
- Grades A/B/C per claim; see the claim registry (GUIDE.md §8, IDs C1–C11).

## The six statements → Lean names, files, grades

| # | Statement | Lean name | File | Grade |
|---|---|---|---|---|
| 1 | NewtonNFc hypotheses → `DescentClaimC` hypotheses | `main_theorem_c_of_claim` | v1/v2 modules | A |
| 2 | `DescentClaimC` ⇐ `ChartEmptyC` (E₄…E₋₂ eliminations) | `chart_descent_refl` | `Descent2R/Main.lean` | A |
| 3 | Stratum b₁₁,₂₀ = 0 has no common zero | `chartEmpty_t1_zero` | `T1Zero/Main.lean` | A |
| 4 | `ChartEmptyC` ⇐ `ChartEmptyC_T1ne0` | `chartEmptyC_of_T1ne0` | `T1Zero/Combine.lean` | A |
| 5 | No common zero on the whole chart | `ChartEmptyC` / `ChartEmptyC_T1ne0` | `T1Zero/Combine.lean` (statement); proved in Lean 2026-11-04 (`challenge_target`, `GradeA.Bridge`) | A |
| 6 | Canonical K₅ certificate size estimate | — (estimate, not a proof) | Hadamard bound (rigorous) × calibrated ratio | C |

## Rank-lemma premises (`branch_c/GUIDE.md` §5.9; paper §10) → scripts

| Premise | Script / output |
|---|---|
| Full row rank of the W = 24 Macaulay matrix (3199 × 6054) mod p at p = 1000003 and 32003 | `chart_certificates/step3b_rank_lift.py`, `step3b_rank_lift.log` (FLINT + numpy agree) |
| Explicit inverse of the 3199 × 3199 pivot block M_S mod 32003, kernel-checked | `branch_c/rank_lemma_check/` → 6398 theorems, axioms `[propext]`, `logs/` |
| Generators are positive integer multiples of the Lean `cond_*` | exact comparison parsed from `CondsC.lean` (in `rank_lemma_check/`) |
| R irreducible over ℚ | FLINT factorization; irreducible mod 67; degree patterns mod 5, 23 |

## Negative controls

| Control set | Location | Result |
|---|---|---|
| T1Zero stratum (C1–C5) | `bundle_v3_1/diag/t1z_controls.py` → `bundle_v3_1/logs/t1z_controls.log` | All 5 fail as required |
| Rank-lemma pivot block | `branch_c/rank_lemma_check/` (`RCControls.lean`, 5 fail + 1 pass) | 5 rejected, 1 passes, axioms `[propext]` |

## What is proved in Lean vs. outside Lean

- **In Lean (grade A)**: statements 1–5; the 6398 pivot-block identities (C9, arithmetic and meaning); the Muse `reduction_lemma` refutation (C7); R irreducible over ℚ (C11, since 2026-10-12).
- **Outside Lean (grade B)**: generator-to-`cond_*` matching (C10, I1 exact comparison). The rank lemma with two-prime, two-implementation ranks, exact input checks, and controls stands as independent corroboration (I1) of statement 5.
- **Estimate (grade C)**: statement 6 (canonical certificate size).

## Explicit non-goals

- Not the Jacobian conjecture, nor any other case of GGHV Prop. 4.3, nor the reduction to it.
- Not an explicit K₅ certificate for the whole chart; only its existence (rank lemma).
- Not a review of the Muse bundle (withdrawn) or the p-adic argument (closed as not needed).
