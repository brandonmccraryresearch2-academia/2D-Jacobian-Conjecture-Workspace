# Manifest — GGHV dependency-closure Lean modules (`gghv-dependency-closure/lean/`)

Filed 2026-11-05 as tracked modules of this repository, from scratch work on
lean-build-3. Every file below was copied byte-identically from
`~/workspace/research/tooling/` (verified with `cmp` at filing time; SHA-256
prefixes below are the first 16 hex digits — run `sha256sum` in this directory
for the full values). No file was edited in filing.

## What "proved" means here (read before citing anything)

- **Kernel-verified** means the Lean kernel accepted the proof of that narrow
  claim, with the axiom list printed by `#print axioms` shown in the log.
  A kernel-verified claim is still only as strong as its hypotheses: a theorem
  proved from carried premises is kernel-verified *conditionally on those
  premises*, and the premises are named per file below.
- **Conditional** means proved from explicit unproved premises carried as
  hypotheses. The premises are part of the theorem statement; they are not
  hidden.
- **The permitted axiom triple** is `[propext, Classical.choice, Quot.sound]`.
  Every `#print axioms` line in every verification log below is either exactly
  this triple, a subset of it, or the zero-axiom verdict ("does not depend on
  any axioms"). `sorryAx` occurs in **none** of the logs (verified by grep,
  2026-11-05). No filed `.lean` file contains the string `sorry` (verified by
  grep, 2026-11-05).
- **Toolchain.** Lean 4.34.0, Lake 5.0.0, Mathlib v4.34.0, on lean-build-3
  (n2-standard-16, us-central1-a). The files were built as scratch with
  `lake env lean --root=/tmp`; they are self-contained cumulative
  developments, **not** a Lake project (there is no `lakefile` here), and they
  are **not** imported by any repo module. Each leg file carries the shared
  infrastructure (direction/valuation definitions `dirVal`, `maxVertDir`,
  `faceTerms`, `crossProd`, `dirLt`, `isDir`, `isSuccFrom`, the Part 17 slice
  layer, `breakpoint_between`) in full, which is why the same infrastructure
  theorem names recur across files; the headline theorems listed per file are
  the new content of that leg.
- **Verification method (parent re-check).** Each leg was re-run independently
  on lean-build-3 in the foreground (full build log `*_parent_recheck.log`)
  and then re-run with an appended `#print axioms` block
  (`*_parent_axioms.log`). The re-check logs contain no `error` lines
  (verified by grep). The axiom counts below are counted from those logs.
  `LEAN_EXIT=0` is the build verdict recorded in the re-check run; where a leg
  needed more than one round, the rounds are listed.

## Filed modules

### 1. `d1_lebasico_full_2026-11-05.lean` — 52,691 bytes, 1,155 lines, sha256 `5869df2341e78bfc`

- **Source:** `~/workspace/research/tooling/d1_lebasico_full_2026-11-05.lean`.
- **Paper:** [GGV1] `le basico` (the paper gives no proof: "completely clear").
  This file is original work, not a transcription of a paper proof.
- **Headline theorems:** `endpoint_slice_max` (closes the vertex-incidence
  gap); `breakpoint_between` (the replacement for the paper's step (B)(ii)
  chord-normal route). The chord-normal route itself is **refuted** by a
  kernel-`decide` counterexample (octagon, ρ₁ = (2, −1), ρ₂ = (−1, 2),
  δ = (4, 3): `isDir` fails); do not retry it. The counterexample is preserved
  in the excluded probe file `d1_leB_counterexample_2026-11-04.lean` (see
  Exclusions).
- **Grade:** kernel-verified. Build rounds: round 1 `LEAN_EXIT=1`
  (superseded), round 2 `LEAN_EXIT=0`.
- **Axioms:** `le_basico_full` depends on axioms
  `[propext, Classical.choice, Quot.sound]` (the permitted triple), per
  `logs/d1_lebbasico_2026-11-05_parent_axioms.log`.
- **Logs:** `logs/d1_lebasico_full_2026-11-05_round1.log`,
  `logs/d1_lebasico_full_2026-11-05_round2.log`.

### 2. `d1_lebbasico_2026-11-05.lean` — 54,910 bytes, 1,198 lines, sha256 `91d92e4d24df25a7`

- **Source:** `~/workspace/research/tooling/d1_lebbasico_2026-11-05.lean`.
- **Paper:** [GGV1] `le bbasico`.
- **Headline theorem:** `le_bbasico` — consecutive directions hold if and
  only if they share a vertex.
- **Grade:** kernel-verified.
- **Axioms:** 2 `#print axioms` lines, both the permitted triple:
  `le_bbasico`, `le_basico_full`.
- **Logs:** `logs/d1_lebbasico_2026-11-05_parent_recheck.log`,
  `logs/d1_lebbasico_2026-11-05_parent_axioms.log`.

### 3. `d1_extremos_2026-11-05.lean` — 70,220 bytes, 1,542 lines, sha256 `14a830a07a0510d1`

- **Source:** `~/workspace/research/tooling/d1_extremos_2026-11-05.lean`.
- **Paper:** [GGV1] `extremos` (the 480 inequality, the 694 aligned case, the
  721 non-aligned case) plus the commutator valuation.
- **Headline theorems (12 in total):** `extremos_alineados` (694),
  `extremos_noalineados_st` and `extremos_noalineados_en` (721),
  `en_sum_eq_one_one` (reusable), `bracket_val_le` (commutator valuation,
  480). The 694/721 statements are at integer `List Term` level, not `KTerm`.
- **Grade:** kernel-verified.
- **Axioms:** 5 `#print axioms` lines — 4 on the permitted triple
  (`extremos_alineados`, `extremos_noalineados_st`,
  `extremos_noalineados_en`, `en_sum_eq_one_one`) and 1 on
  `[propext, Quot.sound]` (`bracket_val_le`).
- **Logs:** `logs/d1_extremos_2026-11-05_parent_recheck.log`,
  `logs/d1_extremos_2026-11-05_parent_axioms.log`.

### 4. `d1_esquina1_2026-11-05.lean` — 168,831 bytes, 3,488 lines, sha256 `073bede8b29d7e23`

- **Source:** `~/workspace/research/tooling/d1_esquina1_2026-11-05.lean`.
- **Paper:** [GGV1] `esquina(1)` (5 theorems in this file; 80 top-level
  `theorem`/`lemma` declarations including the shared infrastructure).
- **Headline theorems:** `esquina_item1` — `Dir` membership and all three
  caso-alineado inequalities; `(a', b')` obtained via Bézout from
  `gcd(m, n) = 1`.
- **Finding recorded in the proof:** the hypothesis `hmn` (`m ≠ n`) is
  **unused** by (1)'s proof — and it is absent from the paper's own proof of
  (1) (Guccione et al. TeX lines 5410–5440). This is a fact about the proof,
  not a gap in it.
- **Grade:** kernel-verified.
- **Axioms:** 3 `#print axioms` lines, all the permitted triple:
  `esquina_item1`, `esquina_esta_en_dir`, `esquina_eqq13`.
- **Logs:** `logs/d1_esquina1_2026-11-05_parent_recheck.log`,
  `logs/d1_esquina1_2026-11-05_parent_axioms.log`.

### 5. `d1_esquina2_2026-11-05.lean` — 141,461 bytes, 2,948 lines, sha256 `8dc4f926772e596c`

- **Source:** `~/workspace/research/tooling/d1_esquina2_2026-11-05.lean`.
- **Paper:** [GGV1] `esquina(2)` (26 theorems in this file).
- **Headline theorems:** `esquina_item2` and `esquina_item2_k1` — with the
  new `succMin` layer; for `k = 1` the pair is `{(−1, 0), (2, 1)}`, which is
  Part 18's form, now **derived** rather than assumed. `succMin_eq` depends
  on no axioms at all.
- **Gap recorded in the proof:** the paper states `m, n ∈ ℕ`, but the proof
  of (2) needs `m, n > 1`. As literally written this is a genuine minor gap
  in the paper; the formalization carries `m, n > 1` as a hypothesis.
- **Grade:** kernel-verified.
- **Axioms:** 4 `#print axioms` lines — 3 on the permitted triple
  (`esquina_item2`, `esquina_item2_k1`, `esquina_proporcionalidad`) and 1
  zero-axiom (`succMin_eq` does not depend on any axioms).
- **Logs:** `logs/d1_esquina2_2026-11-05_parent_recheck.log`,
  `logs/d1_esquina2_2026-11-05_parent_axioms.log`.

### 6. `d1_esquina3_2026-11-05.lean` — 187,822 bytes, 3,877 lines, sha256 `3d44b3d13c68dd55`

- **Source:** `~/workspace/research/tooling/d1_esquina3_2026-11-05.lean`.
- **Paper:** [GGV1] `esquina(3)`, direction half only.
- **Headline theorems:** `esquina_item3_dir`, `esquina_item3_dir_cases`,
  `minkPow_complete` — `(ρ₂, σ₂) = (−1, 3)` at `(−1, 4)/(8, 3)`;
  `b' ∈ {0, 1, 2}`, hence `(a', b') ∈ {(5, 2), (2, 1), (−1, 0)}`;
  primitivity rules out `(−2, 6)` and `(−3, 9)`; support combinatorics
  proved.
- **Not proved:** the `ℓ`-form of esquina(3). Its coefficients are not
  statable at exponent level; it needs central + the Remark + the
  φ-argument + the D2 step. It remains open (see the README's still-open
  list).
- **Grade:** kernel-verified **conditionally on** `hdir`, `hcent`, `hprim`
  (carried hypotheses of the direction statement).
- **Axioms:** 3 `#print axioms` lines, all the permitted triple:
  `esquina_item3_dir`, `esquina_item3_dir_cases`, `minkPow_complete`.
- **Logs:** `logs/d1_esquina3_2026-11-05_parent_recheck.log`,
  `logs/d1_esquina3_2026-11-05_parent_axioms.log`.

### 7. `d1_central_2026-11-05.lean` — 145,961 bytes, 3,242 lines, sha256 `28d36e6d546e1f8f`

- **Source:** `~/workspace/research/tooling/d1_central_2026-11-05.lean`.
- **Paper:** [GGV1] Theorem `central`.
- **Headline theorem:** `central_conditional` — `vF = ρ + σ` with items (2),
  (3), (4) proved. Items (5) and (1) are carried hypotheses, not proved.
  Key lemma `coeffAt_pmul_top_gen2`. The 694/721 statements are proved
  directly at `KTerm` level here.
- **Carried premises (named, not hidden):**
  - Joseph Lemma 2.2 is **not located** in the literature; it is carried as
    hypotheses `hdef`, `hvD`, `hJL`. Homogeneity is load-bearing: the naive
    un-homogeneous form is **false**, with explicit counterexample `B = x`,
    `A = y(x² + 1) + x`.
  - `Lema Joseph` is **not proved**; it is carried as `hneD`, `hDD`,
    `hGchain`. The gap has four named parts: (i) `dim M(t) = (t + 1)²`
    independence, (ii) valuation bounds forcing the `H_j` recursion, (iii)
    termination, (iv) the maximal-`j` step.
  - `[F, ℓ(P)] = ℓ(P)` is **not proved**; it needs a D-cancellation lemma.
- **Grade:** kernel-verified **conditionally** on the carried premises above.
- **Axioms:** 11 `#print axioms` lines — 10 on the permitted triple
  (including `central_conditional`, `central_dichotomy_gen`,
  `central_four_gen`, `valF_from_def`, `endnote_D_mul`,
  `coeffAt_pmul_top_gen2`) and 1 on `[propext]`.
- **Logs:** `logs/d1_central_2026-11-05_parent_recheck.log`,
  `logs/d1_central_2026-11-05_parent_axioms.log`.

### 8. `d1_cor74_2026-11-05.lean` — 182,995 bytes, 4,070 lines, sha256 `5f02daf931947409`

- **Source:** `~/workspace/research/tooling/d1_cor74_2026-11-05.lean`.
- **Paper:** [GGV1] Corollary 7.4 (the F/F1 twins).
- **Headline theorems:** `cor74_F_conditional` and `cor74_F1_conditional`
  (both on the permitted triple). Proved inside the file:
  `valuaciones_G`, `fraction_of_ck3` (derived, not assumed),
  `cor74_exponent` (on `[propext]`), `cor74_assembly` (on
  `[propext, Quot.sound]`), `exists_pow_eq_of_isAlgClosed` (K algebraically
  closed, characteristic 0). The (9, 27) + (7, 21) instances are proved at
  support level **with** condition (3); `ell721_normalization` is proved —
  the true (1, −2)-face is the text support shifted by `x¹⁴`, so the text's
  `R = x²y − λ` lacks an `x` factor (a genuine slip in the paper) and the
  correct identity is `face = λ_p · x¹⁴ · R¹⁴`.
- **Corrections recorded:** Part 19's (8, 28) exponents `4·2 = 8` are wrong —
  `(m, n) = (3, 2)`, so the product is `4·3 = 12`, with the factor 4 from the
  first component and the factor 3 from `m = 3`, giving 12 in full:
  `4 × 3 = 12`.
- **Not proved:** the full polynomial identity `ℓ(P) = R^{qm}` was not proved
  in this file (the D2 power laws that discharge it are in the D2 combine
  leg, file 11 below). Hybrid-vs-slip is open: the published [GGV1] §7 text
  is still missing.
- **Grade:** kernel-verified **conditionally** (condition (3) and the carried
  central premises).
- **Axioms:** 35 `#print axioms` lines — 14 on the permitted triple, 6 on
  `[propext, Quot.sound]`, 13 on `[propext]`, 2 zero-axiom.
- **Logs:** `logs/d1_cor74_2026-11-05_parent_recheck.log`,
  `logs/d1_cor74_2026-11-05_parent_axioms.log`.

### 9. `d1_assembly_2026-11-05.lean` — 29,561 bytes, 593 lines, sha256 `5b6ac33417ecd2b9`

- **Source:** `~/workspace/research/tooling/d1_assembly_2026-11-05.lean`.
- **Paper:** [GGV1] Theorem 2.1, assembled from the §3, §5, and §6 routes
  and the [GGV5] enumeration.
- **Headline theorems:** `theorem21_minimal` — Theorem 2.1 proved from a
  minimal, explicitly enumerated **11-field premise list**; `discard_84_row`
  — the (7, 21) row is eliminated by the §3 route; `table_cases` — the
  case split over the 10-row table. There is **no**
  `theorem21_unconditional`: Theorem 2.1 stays conditional.
- **Key finding:** the (7, 21) row **is** the `max = 84` row (table row 5,
  `⟨(7, 21), 2, 3, 84⟩`). `discard_84` and `discard_721` are two arguments
  for the **same** row, not two rows. The §6 route is not on the minimal
  list: as Part 5 literally defines `discard_721` via §6, it is not
  discharged here; only the `k = 2` degree check is kernel-verified.
- **The 11 fields, in full:** fields 1–5 are the five red rows, carried
  separately ([M] only case 64 is complete — the (5, 20) row; the rest rest
  on [GGV3] §5); field 6 is `link_84` ([GGV6] Theorem 7.3; numerics
  kernel-verified, `I_M = 4`, `I_m = 5`); fields 7–8 are `prop329` +
  `link_120` (§3-120 data kernel-verified; exclusion is kernel arithmetic
  `4 + gcd(8, 4) = 8`, with `gcd(8, 4) = 4`, so `4 + 4 = 8`); fields 9–10
  are `link_924`/`link_927` (§5 endgame kernel-verified; the §5 theorem
  covers both (9, 24) and (9, 27)); field 11 is `enum_complete`, carried.
  (72, 108) is the same (8, 28) row with P/Q exchanged (Keller symmetry),
  so it needs no extra premise.
- **Grade:** kernel-verified **conditionally** on the 11-field list.
- **Axioms:** 3 `#print axioms` lines — `theorem21_minimal` on `[propext]`
  only, `discard_84_row` on no axioms at all, `table_cases` on `[propext]`.
- **Logs:** `logs/d1_assembly_2026-11-05_parent_recheck.log`,
  `logs/d1_assembly_2026-11-05_parent_axioms.log`.

### 10. `d1_ggvstar_2026-11-05.lean` — 250,502 bytes, 5,409 lines, sha256 `e4112d749aee660c`

- **Source:** `~/workspace/research/tooling/d1_ggvstar_2026-11-05.lean`.
- **Paper:** the [GGV*] machinery — [GGV6] Theorem 7.3, [GGV*] Propositions
  3.29, 1.13, 2.1, 2.11, 6.1, Corollary 7.2, Theorem 7.6.
- **Headline results:** the Theorem 7.3 combination + `F₉` arithmetic proved
  (the 84-discard now rests on one carried minor inequality); Proposition
  3.29 proved conditionally from Proposition 3.12 + the starting-vs-end
  instance; the N-bound, the shared-case contradiction, and the identity
  `b + gcd(a, b) = a` proved; Proposition 1.13 both directions proved;
  Proposition 2.1(1) proved; the (8, 24) row conditional on [GGV5]
  Proposition 6.1; the Proposition 6.1 tail arithmetic proved; Corollary 7.2
  conditional.
- **Corrections recorded:** `N₁ = 6`, `N₂ = 3` (integers), **not** the
  brief's `5/3`, `3/2`. Theorem 7.6(5) numbering is unresolved (GGHV's
  "q₁ = 4|d₀" versus the TeX item (4)).
- **Carried:** Theorem 7.6(5), Proposition 2.11(3), Proposition 2.1(2b),
  Proposition 3.12, the enumeration, and 4 of the 5 red rows. Fields 6, 7–8,
  and 5 of the assembly list are discharged one level down; none is
  unconditional.
- **Grade:** kernel-verified **conditionally** on the carried items above.
- **Axioms:** 71 `#print axioms` lines — 37 on the permitted triple, 12 on
  `[propext, Quot.sound]`, 14 on `[propext]`, 8 zero-axiom.
- **Logs:** `logs/d1_ggvstar_2026-11-05_parent_recheck.log`,
  `logs/d1_ggvstar_2026-11-05_parent_axioms.log`.

### 11. `d1_d2combine_2026-11-05.lean` — 319,727 bytes, 6,850 lines, sha256 `1d58861a8bb64ae8`

- **Source:** `~/workspace/research/tooling/d1_d2combine_2026-11-05.lean`.
- **Paper:** [GGV1] the D2 combine step — from the pairwise bracket to the
  combined bracket — plus its three dependent items.
- **Headline theorems (59 new theorems):** the bridge lemma — the combined
  top coefficient equals the endpoint coefficients times the cross product,
  with `k = 1` in the reduced/`Nodup` case; `extremos` (694)/(721) and the
  en-sum in **combined** (paper) form; the D2 power laws (the `pscale` and
  `pbracket` families), which discharge Cor 7.4's carried `hpow`,
  `hscale_pow`, `hppow_mul`; `common_power_coprime` (proved without a UFD);
  the Remark "a remark" proved **conditionally** on `alineados(2a)`
  (Joseph Proposition 2.1(2) — a second Joseph external premise, pinned and
  carried) + `hm₀` + two carried face laws; `mayores` T-termination proved
  (Stage D: Q-degree descent; `[P^i Q^j, P] = −j · P^i Q^{j−1}` by the Keller
  condition, Q-degree −1 per bracketing, with the bidegree correction
  `(i, j) → (i, j − 1)`, not `(i + 1, j − 1)`); `lema_geometrico_1` and
  `lema_geometrico_2` proved.
- **Not done:** the combined-form esquina(1)/(2) restatements (the base
  merge — one mechanical replay); the (7, 21) coefficient identity; the
  univariate UFD lemma (it belongs inside (2a)).
- **Grade:** kernel-verified (the Remark only conditionally, as stated).
- **Axioms:** 72 `#print axioms` lines — 39 on the permitted triple, 11 on
  `[propext, Quot.sound]`, 14 on `[propext]`, 8 zero-axiom.
- **Logs:** `logs/d1_d2combine_2026-11-05_parent_recheck.log`,
  `logs/d1_d2combine_2026-11-05_parent_axioms.log`.

### 12. `d1_d2combine_axioms_2026-11-05.lean` — 321,736 bytes, 6,910 lines, sha256 `8d2b7f9f9354f75f`

- **Source:** `~/workspace/research/tooling/d1_d2combine_axioms_2026-11-05.lean`.
- **What it is:** the D2 combine development of file 11 with a 127-line
  `#print axioms` block appended (60 further lines: the block plus
  surrounding comments). Its header text describes the extremos base the
  file was extended from and is stale; the file's content is the D2 combine
  development, verified by the presence of `common_power_coprime`,
  `lema_geometrico_1`, `lema_geometrico_2`, and the `pscale`/`pbracket`
  families.
- **Grade:** kernel-verified, same content as file 11.
- **Axioms:** the run log `logs/d2combine_axioms_2026-11-05.log` records 126
  verdict lines — 67 on the permitted triple, 30 on
  `[propext, Quot.sound]`, 20 on `[propext]`, 9 zero-axiom — with 0 errors.
  The file's `#print` block has 127 lines for 126 distinct names because
  `stFace_swap` is printed twice (verified by counting distinct names).
- **Logs:** `logs/d2combine_axioms_2026-11-05.log`.

### 13. `bridge_attempt_2026_11_04.lean` — 2,507 bytes, 54 lines, sha256 `b4b4c3985196f462`

- **Source:** `~/workspace/research/tooling/bridge_attempt_2026_11_04.lean`.
- **What it proves:** the bridge between the chart polynomial list and the
  comparator's polynomial list, and the instantiation of the certificate
  interface at the concrete data.
- **Headline theorems, in full:**
  - `bridge_Fpoly : BranchC.GradeA.Chart.Fpoly = BranchC.A2Entry.Fpoly2` —
    the chart `Fpoly` and the comparator's `Fpoly2` are the same six
    `polyOfTerms` generators in the same order (0 = Psi, 1 = Phi1, 2 = Phi2,
    3 = Theta1, 4 = Theta2, 5 = Theta3), built from the single `tl_*`
    definitions in `Chart/Gens.lean`. Proved by `funext n` then `fin_cases n`
    then `rfl`: for each of the six indices `n = 0, 1, 2, 3, 4, 5`, the two
    sides are definitionally equal.
  - `hsupp_chart` — `hsupp2` transported from `Fpoly2` to `Fpoly` along the
    bridge, in exactly the form `chartEmptyC_T1ne0_of_certificate` wants.
  - `hA2_chart` — A2 transported from `Fpoly2` to `Fpoly` along the bridge:
    the Macaulay matrix evaluated at `w₀ = 11147` over `ZMod 32003` equals
    `MS * diagonal(scaleFun)`.
  - `challenge_target {L : Type*} [Field L] [CharZero L] :
    BranchC.ChartEmptyC_T1ne0 L` — the certificate interface instantiated
    at the concrete data `ρ = Fin 3199`, `p = 32003`, `w₀ = 11147`, with the
    six data hypotheses (`hw₀`, `hscale`, `prime32003`, `hmon`, `hr₁`,
    `hsupp2` via `hsupp_chart`) and A1, A2 (`hA2_chart`). R109Data and K5
    were **not** needed.
- **Grade:** kernel-verified, **no hypotheses** (`challenge_target` is
  unconditional as a Lean theorem: it takes no hypotheses beyond the field
  being of characteristic 0).
- **Axioms:** `challenge_target` depends on axioms
  `[propext, Classical.choice, Quot.sound]` (the permitted triple), per
  `logs/bridge_challenge_target_2026-11-04.log`.
- **Logs:** `logs/bridge_challenge_target_2026-11-04.log` (9 lines).
- **Incorporation (2026-11-06):** filed as tracked module `GradeA.Bridge`
  (`JC2D-branches_a_b_c_unified/branch_c/grade_a/lean/GradeA/Bridge.lean`,
  sha256 `96e992d6f4cf2bbfcac33c71e8393700bc2783fc3d6fb5b747a99fc40a1d5c16`),
  compiled and audited by `grade_a/build_bridge.sh`; theorems byte-identical
  to this file (header comment only changed). Re-verified on lean-build-3
  (Lean 4.34.0): baseline re-check + `build_bridge.sh` run 2, all exit 0,
  `challenge_target` on the permitted triple. Status:
  `grade_a/BRIDGE_STATUS_2026-11-06.md`. This leg copy stays as filed.

### 14. `composition_2026-11-04.lean` — 811 bytes, 18 lines, sha256 `59d78bcfc4735084`

- **Source:** `~/workspace/research/tooling/composition_2026-11-04.lean`.
- **What it proves:** branch (c) eliminated, unconditionally (as a Lean
  theorem with no hypotheses beyond characteristic 0).
- **Headline theorem, in full:**
  `branch_c_eliminated {L : Type*} [Field L] [CharZero L] :
  ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNFc P Q ∧
  jac P Q = C lam * X 0 ^ 2` — no Keller pair with Newton normal form (c)
  exists over any field of characteristic 0. It is
  `main_theorem_c_of_chartEmpty_T1ne0` (bundle `Combine`) applied to
  `challenge_target` (file 13).
- **What this does and does not claim:** it eliminates GGHV Proposition 4.3
  case (1) — the case **with** the (0, 8)/(0, 12) vertices, which is
  `NewtonNFc`. Together with the branches (a),(b) `main_theorem`, which
  eliminates case (2) (without those vertices, `NewtonNF2`), the Prop. 4.3
  case split is fully eliminated in Lean. It does **not** claim that
  (72, 108) is excluded unconditionally, and it does not prove JC(2): both
  still rest on GGHV exhaustiveness and the reduction chain, which were
  ledgered, not re-derived.
- **Grade:** kernel-verified, **no hypotheses**.
- **Axioms:** `branch_c_eliminated` depends on axioms
  `[propext, Classical.choice, Quot.sound]` (the permitted triple), per
  `logs/branch_c_eliminated_2026-11-04.log` (1 line).
- **Logs:** `logs/branch_c_eliminated_2026-11-04.log`.
- **Incorporation (2026-11-06):** filed as tracked module `GradeA.Composition`
  (`JC2D-branches_a_b_c_unified/branch_c/grade_a/lean/GradeA/Composition.lean`,
  sha256 `b21a892926dc8d936407c74f6d98bf8393787d3bc1ebd823a56e268bf8587faf`),
  compiled and audited by `grade_a/build_bridge.sh`; theorem byte-identical
  to this file (header comment + one import line changed). Re-verified on
  lean-build-3 (Lean 4.34.0): baseline re-check + `build_bridge.sh` run 2,
  all exit 0, `branch_c_eliminated` on the permitted triple. Status:
  `grade_a/BRIDGE_STATUS_2026-11-06.md`. This leg copy stays as filed.

## Verification logs (`lean/logs/`, 25 files)

- `d1_lebasico_full_2026-11-05_round1.log` (build, `LEAN_EXIT=1`,
  superseded) and `d1_lebasico_full_2026-11-05_round2.log` (build,
  `LEAN_EXIT=0`).
- For each of the ten legs `lebbasico`, `extremos`, `esquina1`, `esquina2`,
  `esquina3`, `central`, `cor74`, `assembly`, `ggvstar`, `d2combine`: a
  `*_parent_recheck.log` (foreground re-run on lean-build-3; no `error`
  lines) and a `*_parent_axioms.log` (the appended `#print axioms` run).
- `d2combine_axioms_2026-11-05.log` (the file-12 axioms run; 0 errors).
- `branch_c_eliminated_2026-11-04.log` and
  `bridge_challenge_target_2026-11-04.log` (the 2026-11-04 lean-build-2
  axiom checks for files 13–14).

## What is NOT filed here (exclusions, with reasons)

The following scratch files were **deliberately excluded**. Each is an excerpt,
a draft, or a probe of a filed leg above; filing them would duplicate content
without adding a theorem. The source files remain at
`~/workspace/research/tooling/`.

**Section excerpts** (each is a byte-subset of the filed leg named; the
headline theorems named appear in both the excerpt and the filed leg, verified
by grep):
- `d1_central_section_2026-11-05.lean` (67,508 bytes) — excerpt of file 7
  (`central_conditional` in both).
- `d1_cor74_section_2026-11-05.lean` (37,033 bytes) — excerpt of file 8
  (`cor74_F_conditional` in both).
- `d1_d2combine_section_2026-11-05.lean` (69,224 bytes) — excerpt of file 11.
- `d1_esquina1_section_2026-11-05.lean` (27,369 bytes) — excerpt of file 4.
- `d1_esquina2_section_2026-11-05.lean` (59,570 bytes) — excerpt of file 5
  (`esquina_item2`, `esquina_item2_k1` in both).
- `d1_esquina3_section_2026-11-05.lean` (18,990 bytes) — excerpt of file 6.
- `d1_extremos_section_2026-11-05.lean` (26,979 bytes) — excerpt of file 3.
- `d1_ggvstar_section_2026-11-05.lean` (67,508 bytes) — excerpt of file 10.

**Drafts and fragments** (superseded by the filed leg):
- `d1_central_stageB_draft_2026-11-05.lean` (23,885 bytes) — a stage-B draft
  of the central leg; superseded by file 7.
- `d1_lebasico_fragment_2026-11-04.lean` (22,481 bytes) — a fragment of the
  le basico development; superseded by file 1.

**Probes** (small test files whose results are recorded in the filed legs):
- `d1_leB_breakpoint_2026-11-04.lean` (18,656 bytes),
  `d1_leB_chord_test_2026-11-04.lean` (2,578 bytes),
  `d1_leB_counterexample_2026-11-04.lean` (6,777 bytes) — probes of the
  `le basico` step (B)(ii) route; the counterexample file holds the
  kernel-`decide` refutation of the chord-normal route recorded under file 1.
- `d1_bridge_test_2026-11-04.lean` (2,794 bytes) — probe of the D1 core
  lemmas; results in files 1–2.
- `d1_cross_pos_test_2026-11-04.lean` (5,370 bytes),
  `d1_dirlt_trans_test_2026-11-04.lean` (2,157 bytes),
  `d1_enface_unique_test_2026-11-04.lean` (3,662 bytes),
  `d1_pos_combo_test_2026-11-04.lean` (3,557 bytes),
  `d1_slice_unique_test_2026-11-04.lean` (1,554 bytes),
  `d1_stface_unique_test_2026-11-04.lean` (3,431 bytes) — probes of the D1
  core lemmas (`isSuccFrom`, `dirLt`, face uniqueness, slice uniqueness);
  results in files 1–2.

## Relation to the grade-A package

The grade-A modules (A1, A2, `hsupp2`, R67Data, R109Data, IrreducibleR,
IrreducibleR109, K5Field, Transfer, Macaulay, Axioms — all 8 modules green,
axioms 22/22, incorporated as commit `03f242f`) already live in this
repository at `JC2D-branches_a_b_c_unified/branch_c/grade_a/` (Lean sources
under `grade_a/lean/GradeA/`). They are **referenced here, not duplicated**:
files 13–14 above import them (`GradeA.Chart.Assembly`, `GradeA.A2Assembly`,
`GradeA.A1Instantiation`, `GradeA.DataHypotheses`, `GradeA.Hsupp`). Do not
copy the grade-A sources into this directory.

## Scope guard

Nothing in this directory proves JC(2), proves Theorem R, or excludes
(72, 108) unconditionally. Theorem R is excluded from this programme. The
CommutingDerivations (OpenAI) file is **not** filed here and is **never** a
kernel check or a premise: it is statement-audited and source-complete with
kernel evidence incomplete. The branch-(c) A1, A2, and `hsupp2` proofs at the
concrete data are the only kernel-verified components counted as such here,
together with the legs listed above at their recorded grades.
