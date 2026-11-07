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

---

## Phase 4 — the GGHV paper proved in full (filed 2026-11-07)

**Honest headline (read first): the paper is NOT proved unconditionally.**
No numbered environment is fully proved unconditionally; Theorem 2.1 is
CONDITIONAL from the 20-field `MinimalPremises2`. Nothing here proves
JC(2), proves Theorem R, or excludes (72, 108) unconditionally. The
definitive per-item verdict record is the filed inventory
`gghv_full_assembly_inventory.md` (1,117 lines); the independent
validation is `validation_g1/g1_validation_report_2026-11-07.md`
(CONDITIONAL GO). This section is the C1 per-file manifest required by
that gate: every filed module below maps to its inventory verdict, its
`#print axioms` list, and its carried premises, with byte sizes and
SHA-256 (first 16 hex digits, as above). Every file below was copied
byte-identically from `~/workspace/research/tooling/` (verified with
`cmp` at filing time, 131 files, zero mismatches). No file was edited in
filing. G1 corrections F1/F2/F3 are applied in the filed inventory
(verified by grep at filing: no stale [GGV5] PDF line citation; the D2 power-law axiom lists
and the E11 C-existence wording are the corrected forms; the [GGV5]
citation is pdftotext l.2927).

Toolchain for all Phase 4 legs: Lean 4.34.0, Lake 5.0.0, Mathlib
v4.34.0, on lean-build-3 (n2-standard-16, us-central1-a, 16 vCPUs /
64 GB). All leg files are self-contained (`import Mathlib` only, no
cross-file imports, no `sorry`, no `axiom` declarations — grep-verified
at filing: the only "sorry" hits are header-comment words). The
`[triple]` abbreviation is `[propext, Classical.choice, Quot.sound]`.

### Phase 4.1 — Leg A: `gghv_full_s2s3_2026-11-06.lean` — 29,733 bytes, 645 lines, sha256 `ed23c0e5323c6d6e`

- **Source:** `~/workspace/research/tooling/phase4_legA/`.
- **Paper:** GGHV §2 table + §3 discards (max = 120, 84).
- **Verdict:** KERNEL table arithmetic (`gghv_table_full` [],
  `discard_84_row` [], `discard_120_row` []); red rows CONDITIONAL
  (carried to Leg F); table completeness BLOCKED.
- **Axioms:** 21 theorems: 10 [] + 4 [propext] + 5 [triple] + 2
  [propext, Quot.sound] (`legA_axioms.log`, AXIOMS_EXIT=0, 6 s).
  FULL_EXIT=0, 6 s (`legA_full.log`). `survivors_exact` [propext].
- **Carried premises:** the §3 discards' external links (`prop329`,
  `link_120`, `link_84`); [GGV5] enumeration completeness.
- **Second tool:** `check_legA_2026-11-06.py`, 28 checks ALL PASS,
  exit 0 (filed in `lean/logs/`).
- **Correction note:** Leg A's file header claims the local [GGV5] TeX
  §6 is "Program and graphic display" and contains no Proposition 6.1
  under that number. That claim is WRONG for the only [GGV5] source on
  disk and for arXiv v1 (inventory §8; TeX l.1874, PDF pdftotext
  l.2927). The filed leg file is a dated record and is NOT rewritten;
  do not repeat the header claim. The (8,24) red-row premise itself is
  unaffected in substance (Prop 6.1 exists under that number in arXiv
  v1; its numbering is UNVERIFIED for any published version).

### Phase 4.2 — Leg B: `gghv_full_s4_2026-11-06.lean` — 65,301 bytes, 1,378 lines, sha256 `51d169312d4841be`

- **Source:** `~/workspace/research/tooling/phase4_legB/`.
- **Paper:** GGHV §4, Props 4.1–4.4 + Algorithm PossibleStartingPoints
  (E5–E9).
- **Verdict:** E5–E8 CONDITIONAL; E9 KERNEL (implementation + output),
  correctness CONDITIONAL.
- **Axioms** (10 `#print axioms`, in `legB_log.md`; no separate
  FULL/AXIOMS log files were produced by this leg — the log is the
  record): `prop41_conditional` [propext, Quot.sound] (l.407);
  `prop42_conditional` [triple] (l.753); `prop43_conditional` [propext,
  Quot.sound] (l.1088); `prop44_conditional` [triple] (l.1315);
  `psp_183` [propext] (l.494); `sieve_table_927` [propext];
  `ell721_normalization` [propext, Quot.sound]; `phiJacPair_3` /
  `phiJacPair_4` []. `sorryAx` NOWHERE. Final run FULL5_EXIT=0, 8 s,
  0 errors (earlier runs 1–2 failed on real bugs, fixed; see the log).
- **Carried premises:** `Prop41Premises` (Cor 7.4 edge step, φ₃ edge
  step, Prop 8.2 applied instance); `Prop42Premises` ([GGV2] Prop 3.12
  soundness, [vdE] Prop 10.2.6, Prop 3.12(2), hybrid-vs-slip);
  `Prop43Premises` ([GGV6] Prop 2.5, [GGV2] Prop 3.12 setting,
  hybrid-vs-slip, k=2 exclusion, Succ determination);
  `Prop44Premises` (Cor 7.4 (q=7) φ₂-cut link). The polynomial-level
  statement is NOT claimed (Laurent layer R14).
- **Second tool:** `check_s4_second_tool.py` (Python 3.11.2), ALL PASS
  20/20, PY_EXIT=0 (first run FAILED 2/20 on a script bug — divisibility
  backwards; Lean file + paper were right; fixed and re-run).

### Phase 4.3 — Leg C: `gghv_full_s5_2026-11-06.lean` — 43,525 bytes, 836 lines, sha256 `f7137faf2ddc5285`

- **Source:** `~/workspace/research/tooling/phase4_legC/`.
- **Paper:** GGHV §5, Thm 5.1 + `calculo de C` (E10–E17).
- **Verdict:** E10 CONDITIONAL; E11 PARTIAL (see Laurent §4.10);
  E12 PARTIAL; E13 KERNEL; E14 CONDITIONAL; E15 KERNEL arithmetic +
  CONDITIONAL bounds; E16 KERNEL (elimination only), derivation OPEN;
  E17 CONDITIONAL.
- **Axioms:** 39 declarations: 30 [triple] + 5 [propext, Quot.sound] +
  2 [propext] + 2 [] (`s5_axioms.log`, LEAN_RC=0). Headlines:
  `thm51_conditional` [triple] (l.793); `cor52_conditional` [];
  `e13_f_separable` [triple], `e13_bezout` [triple];
  `e16_principal` [triple], `e16_cert` [propext, Quot.sound];
  `e14_d_mem` [triple]; `e15_bound_neg13` / `e15_bound_17` [propext,
  Quot.sound]; `e12_remark_conditional` [triple] (l.500);
  `e11_recursion_step` / `e11_recursion_sign_slip` [triple].
  FULL LEAN_RC=0, 42 s, 0 errors, 0 sorryAx (`s5_build_5.log`, the
  final build log).
- **Carried premises:** the §5 data link (rescaling inputs,
  coefficient-system derivation, 9-equation derivation, [GGV1] Props
  1.13/2.1); the convolution identity (E14); E11(3)/(4) + x-monomial
  valuations (E15); hJac/hFace (E12).
- **Second tool:** E13 Singular 4.3.1 rc=0 (ODE_DIFF = 0, GCD_F_FP = 1)
  and SymPy (see `singular/logs/e13_*`); φ-shift confirmed by both
  tools (x²-coefficient D₂−3t; t=D₂ gives −2D₂, t=D₂/3 gives 0).
  Caveats are logged, not hidden: the filed SymPy script exits rc=1
  with DECOMPOSED defects (2× gcd Poly-domain artifacts, 1× bracket
  script error with factor 2, 3× dsolve limitations); ODE uniqueness
  among polynomials via dsolve is NOT ESTABLISHED (not refuted).

### Phase 4.4 — Leg C axioms file: `gghv_full_s5_axioms_2026-11-06.lean` — 44,656 bytes, 875 lines, sha256 `68593452234f4163`

- The `#print axioms` companion to §4.3 (the 39 `#print axioms` lines
  appended to the §5 file). Log `s5_axioms.log`. No new theorems.

### Phase 4.5 — Leg D: `gghv_full_s6_2026-11-06.lean` — 77,734 bytes, 1,613 lines, sha256 `7c9e2b3842a26451`

- **Source:** `~/workspace/research/tooling/phase4_legD/`.
- **Paper:** GGHV §6, Thm 6.1 + `calculo de C para 7` (E18–E23).
- **Verdict:** E18 CONDITIONAL; E19 PARTIAL (see Laurent §4.10);
  E20 KERNEL modulo Ptcoef input data; E21 CONDITIONAL; E22 KERNEL
  (elimination/displays only), derivation OPEN; E23 PARTIAL.
- **Axioms:** 80 theorems: 64 [triple], 8 [propext, Quot.sound], 8 []
  (`s6_axioms3.log`, FINAL axioms run EXIT 0). Headlines:
  `s6_theorem61` [triple] (l.1577); `s6_principal_eq` [triple]
  (l.954); `e23_ode_unique` [triple] (l.383); `e20_assembly` [propext,
  Quot.sound] (l.498); `e21_membership` [triple] (l.1455);
  `e19_recursion` [triple] (l.247). FINAL FULL EXIT 0, ~14 s, 0 errors
  (`s6_full6.log`). No sorryAx.
- **C1(a) — ValAxioms diagnosis (G1 condition, read before citing
  anything from this file):** `e19_bound_step_21` [triple] (l.171),
  `e19_bound_step_1m1` [triple] (l.206), `e19_finite_bounds` [triple]
  (l.268) are **kernel-proved implications, NEVER instantiable with
  v_{2,1}/v_{1,−1}** — do not cite them as instantiated. Leg D's
  `ValAxioms` structure is uninstantiable: unconditional `mul`
  forces w ≡ 0 (`ValAxiomsOrig.forces_zero`, [propext, Quot.sound],
  Laurent fragment l.116), and `add` forces w ≥ 0, inconsistent with
  any valuation taking a negative value. The usable bound steps are
  the Laurent fragment's `valcore_*` versions (KERNEL from `ValCore`),
  instantiated at `valCore_lpMaxDeg` / `valCore_lpMinDeg` (§6).
- **Carried premises:** 9 equations + degrees (hd0deg, hd1deg) +
  dm1≠0 + hsq (non-square premise — Singular-supported up to the
  nonzero factor y⁹, no explicit lift coefficients); `y ∣ P₅` (the
  D₂ base case, E21); Prop 4.4 reduction (Leg B, E8).
- **Second tool:** Singular 4.3.1 elim/cert/Gröbner re-runs exit 0
  (see `singular/logs/*_s6_rerun.log`, `member_*.log`).
  `lift_s6_extra.sing` TIMEOUT 600 s (exit 124) — inconclusive, and
  its Q4x2 carried a 6/6 transcription error (fixed to 12/12);
  explicit lift() coefficients still NOT obtained.

### Phase 4.6 — Leg D axioms file: `gghv_full_s6_2026-11-06_axioms.lean` — 79,486 bytes, 1,688 lines, sha256 `a8b2bf542bb9b447`

- The `#print axioms` companion to §4.5 (80 `#print axioms` lines).
  Log `s6_axioms3.log`. No new theorems.

### Phase 4.7 — Leg E: [GGV1]/[GGV*] remainder (R8–R17), 10 item files + index

- **Source:** `~/workspace/research/tooling/phase4_legE/`.
- **Verification:** per-file FULL 7–14 s, exit 0, Lean 4.34.0; 87
  declarations across the item files; `sorry` grep over all .lean
  files: only comment mentions; no `axiom` declarations in code.
  Second tool: Python 3.11.2 `second_tool_checks.py` ALL PASS, exit 0
  (19 checks); Singular 4.3.1 `jacobi_check.sing` JACOBI = 0,
  BRACKET_AB = −x²−1, exit 0. Logs in `lean/logs/` (per-file FULL +
  AXIOMS; the index file has a FULL log only — see below).
- **No renames:** all filenames use underscores (no hyphens); the
  index file imports nothing and no item file imports another — each
  is self-contained (`import Mathlib` only).

#### `gghv_full_esquina3l_2026-11-06.lean` (R8) — 6,672 bytes, 139 lines, sha256 `7299591fb85b5889`

- **Verdict:** KERNEL (arithmetic + ℓ-form assembly); the ℓ-form
  itself CONDITIONAL on its named premises.
- **Axioms** (`gghv_full_esquina3l_2026-11-06_axioms.log`):
  `esq3_val_8_3` []; `esq3_mn_sum` [propext, Quot.sound];
  `esq3_dir_determination` [triple];
  `esq3_phi_aligned_impossible` [propext, Quot.sound];
  `esq3_phi_nonaligned_impossible` [propext, Quot.sound];
  `esq3_lform_term_val` [propext]; `esq3_lform_from_cube` [propext,
  Quot.sound]; `esq3_dir_b2` / `esq3_dir_b1` / `esq3_dir_b0` [];
  `esq3_lform_endpoint_lo` / `esq3_lform_endpoint_hi` [propext];
  `esq3_lform_Q` [propext, Quot.sound]. The six endpoint/Q theorems
  were re-printed by the assembly R8 run (`r8_axioms.log`, rc=0,
  15 s) with identical lists.
- **Carried premises:** `esq3_lform_from_cube` is CONDITIONAL on the
  common-power premise `ℓ(P) = λ_P R^m` and the cube premise
  `x·R = c·(z−μ)³` (not proved — the φ-argument and the cube premise
  itself are carried). NOT proved: the identification of
  `ℓ_{−1,3}(P)` with the face polynomial in the KTerm list model.

#### `gghv_full_central_gaps_2026-11-06.lean` (R9) — 9,879 bytes, 189 lines, sha256 `fd58a01743f62e8c`

- **Verdict:** KERNEL + CONDITIONAL.
- **Axioms:** `central_cancellation` [propext]; `central_item5`
  [propext]; `joseph_counting_contradiction` [propext, Quot.sound] +
  `int_interval_card` [triple] (Lema Joseph dimension-counting
  arithmetic). CONDITIONAL: `central_eq_central_from_joseph22`
  [propext] on the named `Joseph22HomogForm` premise (homogeneous
  form only).
- **Carried premises:** Joseph Lemma 2.2 itself — NOT FOUND
  (retrieval leg, 12 routes); the naive un-homogeneous form is FALSE
  (counterexample in the dated log). Central item (1) (`F ∈ L`) is the
  `sub F` component of the conditional theorem.

#### `gghv_full_esquina_combined_2026-11-06.lean` (R10) — 5,964 bytes, 122 lines, sha256 `3395568957a17315`

- **Verdict:** KERNEL.
- **Axioms:** `esquina2_set_iff`, `esquina2_combined`,
  `esquina2_k1_pair` [triple] each; `esquina1_bundle_iff` [].
- **Carried premises:** none (combined-form restatements).

#### `gghv_full_721_coeff_2026-11-06.lean` (R11) — 7,162 bytes, 138 lines, sha256 `06730e89f4a50e2e`

- **Verdict:** KERNEL.
- **Axioms:** `face721_*` (base identity, coeffs, monic, natDegree,
  leading coeff, remainder degree) [triple] each;
  `face721_factor_count` [propext].
- **Carried premises:** none for the stated identity; the general-`m`
  second coefficient is open (its step-1 bound is kernel).

#### `gghv_full_remark_facelaws_2026-11-06.lean` (R12) — 4,702 bytes, 96 lines, sha256 `acb5d85f24e2a617`

- **Verdict:** KERNEL.
- **Axioms:** `alineados_2a_from_2b`, `remark_ratio`,
  `remark_st_scaling`, `remark_en_scaling` [triple] each;
  `tpow_exp_smul` [propext, Quot.sound].
- **Carried premises:** consequences (1)(2)(3) are kernel conditional
  on the power-law premises; the general face law is carried.

#### `gghv_full_d1_theory_2026-11-06.lean` (R13) — 7,581 bytes, 160 lines, sha256 `826f4859e0083f28`

- **Verdict:** KERNEL.
- **Axioms:** `dirLt_trans_halfplane` [triple];
  `dirLt_irrefl'` [propext]; `dirLt_asymm'` [propext, Quot.sound];
  `succ_set_consecutive` []; `succOp_eq_of_isSuccFrom` +
  `succOp_spec` [triple]; `cross_dot_identity` [propext,
  Quot.sound].
- **Carried premises:** Succ-as-operator is kernel modulo explicit
  premises; the `stFace`/`enFace` ↔ CCW bridge is still open.

#### `gghv_full_d2_poly_2026-11-06.lean` (R14) — 7,955 bytes, 170 lines, sha256 `fb72fbab116436aa`

- **Verdict:** KERNEL.
- **Axioms:** `pderiv_comm`, `pbracket_antisymm/add_left/add_right/
  smul/leibniz/jacobi/translate`, `joseph_counterexample_bracket`,
  all [triple].
- **Carried premises:** the translation chain rule is conditional on
  the `pderiv`/`aeval` commutation.

#### `gghv_full_mn_gt1_2026-11-06.lean` (R15) — 3,852 bytes, 73 lines, sha256 `77682c7edea79696`

- **Verdict:** KERNEL as documented deviation.
- **Axioms:** `mn_gt1_dir_mem` [triple]; `mn_eq1_needs_b_gt1` [];
  `gghv_uses_mn_gt1` []; `gghv_uses_dir_mem` [triple].
- **Carried premises:** none — the finding IS the deviation: the
  paper states m,n ∈ ℕ but esquina(2)'s proof needs m,n > 1, a
  genuine minor gap as literally written (published §7 wording NOT
  FOUND; arXiv-TeX wording flagged as NOT the published wording).

#### `gghv_full_hybrid_slip_2026-11-06.lean` (R16) — 3,587 bytes, 70 lines, sha256 `eca429ff9a9d39d5`

- **Verdict:** KERNEL arithmetic; question OPEN.
- **Axioms:** `hybrid_arith_249/288`,
  `hybrid_slot_249/288/927/721` [triple] each.
- **Carried premises:** the hybrid-vs-slip question itself stays OPEN
  (published §7 NOT FOUND); both readings are stated explicitly.

#### `gghv_full_mayores_2026-11-06.lean` (R17) — 5,143 bytes, 104 lines, sha256 `28b8cb293f88e42a`

- **Verdict:** KERNEL / CONDITIONAL.
- **Axioms:** `mayores_termination_descent` [propext];
  `mayores_chain_terminates` [propext, Quot.sound];
  `mayores_cocientes_ratio` [triple];
  `mayores_cocientes_conditional` + `mayores_full_conditional`
  [triple].
- **Carried premises:** the two `_conditional` theorems carry their
  named premises (see the file).

#### `gghv_full_ggv1_2026-11-06.lean` (Leg E index) — 2,504 bytes, 43 lines, sha256 `83716cd47a9561ba`

- Comment-only index/header for Leg E (lists the 10 item files and
  their R-numbers). It contains NO theorems and NO `import` lines, so
  there is no axioms log for it — only the FULL log
  (`gghv_full_ggv1_2026-11-06_full.log`, exit 0). It is filed as the
  leg's index, not as a proof file.

### Phase 4.8 — Leg F: [GGV*] machinery (R18–R20), 3 files

- **Source:** `~/workspace/research/tooling/phase4_legF/`.
- **Verification (round 5, final):** all three files LEAN_EXIT=0, 0
  error lines, NO sorryAx (logs in `lean/logs/`, round-5 run2 files).
  md5s recomputed at filing and matching the inventory exactly:
  File 1 `5db7b34420dcf8d111223e79aaed3f44`, File 2a
  `2e61236431142905b92d09252d1251f9`, File 2b
  `159527f8326bf32e87276651054c5fcf`. The one "sorry" grep hit per
  file is a header comment stating no `sorryAx` is in the file.

#### `gghv_full_ggvstar_2026-11-06.lean` (File 1: [GGV2] Prop 3.12) — 265,445 bytes, 5,686 lines, sha256 `6ec4bcea80acf5c2`

- **Verdict:** Prop 3.12 CONDITIONAL; Prop 3.29 / Remark 3.31 /
  Def 3.21 CONDITIONAL (see below).
- **Axioms** (round-5 run2): `finitas_of_data` [triple] (l.5469);
  `prop329_of_data` [triple] (l.5593); `remark331_of_data` [triple]
  (l.5625); `llc_imp_pllc` [triple] (l.5658);
  `llc_84_excluded_of_data` [triple].
- **Carried premises:** `FinitasData` (l.5293) — the paper's cited
  lemmas as named premises (Lemma `factores en jacobiano` eq2, Lemma
  `maximo grado`, [GGV1] Prop 1.13, Remark `gap`, [GGV1] Prop 2.4(1)
  dichotomy); `prop329_of_data` is conditional on
  FinitasData-existence per AdmStep + hSE (starting-vs-end instance);
  `remark331_of_data` carries the (10,25)/(14,35) forcing (paper:
  "without a formal proof"); `llc_imp_pllc` carries the maximality
  clause (the base's "Def 3.21 = AdmChain + PLLC" was CORRECTED:
  LLC = PLLC + pair-origin condition).

#### `gghv_full_ggvstar_ggv1_2026-11-06.lean` (File 2a: [GGV1] Thm 7.6(5), Prop 2.11(3), Prop 2.1) — 234,718 bytes, 5,119 lines, sha256 `1aab45bbf3b58512`

- **Verdict:** Thm 7.6(5) CONDITIONAL; Prop 2.11(3) CONDITIONAL;
  Prop 2.1(2b)→(2a) KERNEL-clean; (2a)→(2b) BLOCKED; D2 power laws
  PROVED.
- **Axioms** (round-5 run2): `divisibilidad_gghv_use8` and
  `divisibilidad_gghv_use8_of_arxiv` [triple] (ll.4714/4725);
  `pavadass3_of_descended` [triple] (l.4832);
  `prop21_two_a_of_b` [triple] (l.5065);
  `coeffAt_pmul_assoc` **[propext, Quot.sound]** (l.4939) —
  **G1 correction F1:** this is NOT [triple]; `ppow_add_kt`
  [triple] (l.5020); `ppow_mul_kt` [triple] (l.5050). All three
  power laws are still kernel-proved (a [propext, Quot.sound] list
  is a subset of the permitted triple); the correction is to the
  quoted list only.
- **Carried premises / blockers:** Thm 7.6(5): numbering
  identification `h76_5` (published numbering UNVERIFIED — published
  §7 text NOT FOUND) + corner-index identification; Prop 2.11(3):
  hproc (multiplicity-procedure premise); direction CORRECTED — item
  (3) is a DESCENT, not the ascent the base pinned. (2a)→(2b)
  BLOCKED on the univariate common-power lemma (fⁿ = α·gᵐ,
  gcd(m,n)=1 ⇒ f,g powers of a common polynomial) + the z-form
  reduction (P = x^{r/l}y^s f(z), rational exponents, not in the
  KTerm layer).

#### `gghv_full_ggvstar_ggv6_ggv5_2026-11-06.lean` (File 2b: [GGV6] Thm 7.3, [GGV5] completeness, red rows) — 265,506 bytes, 5,700 lines, sha256 `273a238316909cf1`

- **Verdict:** [GGV6] Thm 7.3 NOT PROVED as a theorem; [GGV5]
  completeness BLOCKED; four red rows CONDITIONAL; (8,24) row
  CONDITIONAL on [GGV5] Prop 6.1.
- **Axioms** (round-5 run2): `ggv6_discard84_from_thm73` [triple]
  (l.5458); `enum_complete_of_links` [triple] (l.5529);
  `pllc_finite_of_cota` [triple] (l.5510);
  `redrow_412_34_conditional` [triple] (l.5591);
  `redrow_412_57_conditional` [triple] (l.5603);
  `redrow_520_23_conditional` [triple] (l.5616);
  `redrow_520_32_conditional` [triple] (l.5640);
  `redrow_520_32_of_23` []; `redrow_824_conditional` (l.5419).
- **Carried premises / blockers:** `ggv6_thm73_stmt` (l.4664) is a
  `def` (pinned statement), not a proved theorem — the combination
  is proved in the base; the theorem needs the [GGV6] §7 argument
  over the π-root existence theory. `enum_complete_of_links` is
  CONDITIONAL on two OPEN links: `hchain` (pair-to-chain
  construction) and `hattrib` (PLLC-to-table attribution).
  `pllc_finite_of_cota` is CONDITIONAL on `para_la_cota` (the next
  attackable premise). Red rows are conditional on the cited external
  discards ([GGV4] §3.5 published / [M] case 64 / [H] / [GGV3] §5;
  (5,20)/(3,2) via P/Q swap, swap-closure as explicit hypothesis).
  [GGV4] §3.5 flag: the arXiv version (arXiv:1310.8249) contains NO
  (4,12) discard — the citation must refer to the PUBLISHED version's
  §3.5 (Pro Mathematica 27 (2013) 83–98).

### Phase 4.9 — Assembly: `gghv_full_assembly_2026-11-06.lean` — 155,137 bytes, 3,165 lines, sha256 `4a845f3b5e17e8bf`

- **Source:** `~/workspace/research/tooling/phase4_assembly/`.
- **Verdict:** Theorem 2.1 CONDITIONAL from the 20-field
  `MinimalPremises2`; fields 9–10 REFINED into named chains (not
  unconditionally discharged).
- **Axioms** (assembly run 2026-11-07 ~02:08 UTC, lean-build-3):
  `theorem21_minimal_v2` [triple] (l.3108);
  `link_924_derived` [triple]; `link_927_derived` [triple];
  `prop42_shape_of` [triple]; `prop41_shape_of` [propext,
  Quot.sound]. Re-verified in the same run (matching the legs' own
  lists): `prop41_conditional` [propext, Quot.sound],
  `prop42_conditional` [triple], `prop43_conditional` [propext,
  Quot.sound], `prop44_conditional` [triple], `thm51_conditional`
  [triple], `cor52_conditional` []. FULL_EXIT=0, 135 s, 0 errors
  (`assembly_full.log`, 36,472 bytes; 98 warnings, all linter /
  deprecation noise); AXIOMS_EXIT=0, 50 s, 0 errors
  (`assembly_axioms.log`, byte-identical to the FULL log — the same
  file compiled twice with the same `#print` block). No sorryAx.
- **Carried premises:** `MinimalPremises2` fields 1–8 and 11 unchanged
  (red rows, [GGV6] Thm 7.3 + π-root machinery, [GGV2] Prop 3.29,
  last-possible-corner computation + Thm 7.6(5) numbering, [GGV5]
  completeness); fields 9–10 refined into `prem42`/`bridge924`/
  `link51_924` and `prem41`/`bridge927`/`link52_927`/`link51_927`
  (bridges = polynomial lifts, Laurent layer R14; §5 data links).
  The bridge and the §5 link stay carried because Leg B's
  conditionals are vertex-list level only and Leg C's
  `thm51_conditional` is kernel only given its link hypothesis.

### Phase 4.10 — Laurent fragment: `gghv_full_laurent_2026-11-06.lean` — 83,349 bytes, 1,705 lines, sha256 `90e9486b37af7e8c`

- **Source:** `~/workspace/research/tooling/phase4_laurent/`.
- **Verdict:** E11 PARTIAL; E19 PARTIAL (existence + bounds KERNEL,
  F CONDITIONAL); E20 KERNEL modulo Ptcoef input data; E23 PARTIAL
  (monomial bracket + ODE uniqueness KERNEL, series-bracket reduction
  CONDITIONAL on `hdeg`).
- **Axioms:** full-file audit AX_FULL_RC=0, 87 theorems, sorryAx 0
  (86 "depends on axioms" lines + `pow_ne_zero_of_ne` []).
  Headlines: `exists_sqrt_series` [triple] (l.868);
  `laurent_series_discharge_s6` [triple] (l.1541);
  `exists_tilde` / `tilde_discharge` (l.1591);
  `bracket_reduction_discharge` (l.1612, conditional on `hdeg`);
  `f_discharge` (l.1623, conditional on `GGV1Inputs`);
  `f_discharge_lp_s6` (l.1681, conditional on `GGV1InputsLp` +
  unit); `ValAxiomsOrig.forces_zero` [propext, Quot.sound] (l.116).
  Non-triple lists are all subsets (`ValAxiomsOrig.*` [propext,
  Quot.sound], `ValCore.inv_unit` [propext, Quot.sound],
  `ValCore.pow` [propext], `valcore_b0_21` [propext]).
  FINAL_FULL_RC=0, 0 errors, ~10 s (`laurent_log.md`).
- **C1(d) — first-attempt failure, recorded (G1 condition):** the
  first AX_FULL attempt failed at RC=1 with 7 errors (generated
  `#print axioms` names in the wrong namespaces); the names were
  fixed and the audit re-run clean. Only the final clean run is the
  verification record; the failed attempt is recorded here so the
  record is complete. The failure is in `laurent_log.md` /
  `laurent_err.txt`.
- **C1 — E11 wording (G1 correction F2):** C-existence is the
  **generic sqrt-series lemma KERNEL** (`exists_sqrt_series`
  [triple]); the §5 instance (A := RatFunc K, u0 := C₃ = y⁸(y+1))
  is NOT separately applied — instance application remains open.
  §5 (b_k)/(c_k) bounds are NOT discharged (min-degree ValCore on
  RatFunc K missing). The fragment's only applications of the generic
  lemma are the §6 instance (l.940) and the tilde instance (l.1482).
- **Second tool:** Python/Fractions `recursion_check.py`
  (filed as `lean/logs/laurent_recursion_check.py`) — convolution
  identity (u*u)_n = q_n for n = 0..5: PASS.
- **Precise remainders:** §5 (b_k)/(c_k) bounds (needs a min-degree
  ValCore on RatFunc K); Leibniz rule for `LaurentSeries.derivative`
  (needed for `bracket_pow_C` and `hdeg`; absent from Mathlib
  4.34.0); the paper's sharper Ft claim (Ft has v10 = −4, lam' =
  lam − α₁²/3 + …) is NOT proved (Ft is defined as the difference).
  Premises that do NOT fall: `bridge924`/`bridge927` (polynomial
  lifts), `link51_924`/`link51_927` (§5 data links), E14's
  convolution identity, E15's bounds, E10's premises, E23's `hdeg`.

### Phase 4.11 — R8 axioms file: `r8_axioms_2026-11-06.lean` — 6,852 bytes, 146 lines, sha256 `9d9b97bce24e2a617`

- The `#print axioms` companion for the six R8 endpoint/Q theorems
  (see §4.7, R8): `esq3_dir_b2/b1/b0` []; `esq3_lform_endpoint_lo/hi`
  [propext]; `esq3_lform_Q` [propext, Quot.sound]. Run 2026-11-07
  ~02:08 UTC, rc=0, 15 s, 0 errors (log `r8_axioms.log`, 1,088 bytes).
  `esq3_lform_from_cube` is conditional on its named premises
  (common-power premise + cube premise), as recorded in §4.7.

### Phase 4.12 — Leg H: explicit maximal minor (PARTIAL, narrowed)

- **Source:** `~/workspace/research/tooling/phase4_legH/`.
- **Filed location:** `JC2D-branches_a_b_c_unified/branch_c/
  rank_lemma_check/` (the existing layout — that directory already
  holds the branch-(c) matrix material, including the tracked
  `INVERSE.pkl`).
- **Verdict:** PARTIAL, narrowed (Step 3). This leg produces an
  identification (I1 on the shared matrix construction), not a kernel
  proof; it does not change any Lean grade.
- **C1(b) — filed as PARTIAL (G1 condition):** indices + modular
  determinant values are DONE; the determinant value as an explicit
  element of K₅ (5 rational coefficients) is NOT DONE — no feasible
  route exists (would need the 3199×3199 determinant over ℚ[w]/(R),
  i.e. multimodular reconstruction over ~10⁴ primes). Whether the
  delivered form satisfies §6.3(a) as literally worded is
  **Brandon's judgement call** (this gate does not decide it).
  Outside-project rebuild (§6.3b) is NOT DONE. A Lean formalization
  of this minor (`RingHom.map_det` instance) is un-ordered.
- **Filed files (sizes + SHA-256, first 16 hex):**

| File | Bytes | sha256 |
|---|---|---|
| `minor_spec_2026-11-06.md` | 13,895 | `6896a7ec92804a4f` |
| `extract_minor.py` | 5,418 | `0bbe36b10f9659cc` |
| `det_minor.py` | 6,193 | `c49eb267466d8874` |
| `legH_log_2026-11-06.md` | 4,814 | `a6ee5f8520c3e49f` |
| `rows.json` | 54,834 | `b8b5f3431d0e2c15` |
| `piv.json` | 18,084 | `00e40995b010f30a` |
| `pivcols.json` | 86,447 | `bdc3cba8d26cd0bc` |
| `colv.json` | 1,510,086 | `d6498dc5a7c8bc12` |
| `det_p32003.json` | 264 | `2a6b850ff7c0d0b7` |
| `det_p1000003.json` | 216 | `2fde0a9dc56576aa` |
| `det_p32003.log` | 141 | `95eca6fee71bdfbe` |
| `det_p1000003.log` | 91 | `b0e1fb330b5312f5` |
| `globals.txt` | 109 | `f1a3ef5013d2b6f4` |
| `summary.json` | 685 | `9b0575e252c42415` |
| `logs/build_p1000003.log` | 539 | `74323415bbcde077` |
| `logs/det_p32003.log` | 182 | `127199b7a7c4ee16` |
| `logs/det_p1000003.log` | 215 | `5c61849d55a3fd47` |
| `logs/extract.log` | 1,019 | `1300234ffdd506af` |
| `logs/mcheck.log` | 264 | `997249b0a40137fa` |

- **Determinants (verified on disk by the assembly agent):**
  p=32003, w₀=11147 → det = 29127 (FLINT = NumPy-LU, routes agree,
  detC = 9069, detC×det ≡ 1 mod 32003); p=1000003, w₀=806739 → det
  = 262898 (both routes agree). Timings 4.6 s / 193.4 s and 4.8 s /
  201.4 s. Matrix M₂₄: 3199 rows × 6054 columns, 239,154 nonzeros,
  over K₅ = ℚ[w]/(R), R = w⁵ − w⁴ + 3w³ + 3w² + 26. Row set: all
  rows 0–3198 in filed order; column set: the 3199 FLINT-RREF pivot
  columns. Both determinant scripts exit 0 and assert route
  agreement (aborting on disagreement). VM: lean-build-3, Python
  3.11.2, python-flint 0.9.0, numpy 2.4.6.
- **INVERSE.pkl is NOT re-filed here.** The 79 MB binary
  (`branch_c/rank_lemma_check/INVERSE.pkl`, 82,788,865 bytes, file
  sha256 `1af9b3c8a4d32a2a611b6b3958c6e3770e282d5d351b423af45ea304a44189fe`)
  is already tracked in this repository (since 2026-10-31) and is
  referenced by path + sha256 only. NOTE (resolves a record
  ambiguity): the Phase 3 "sha256 `00e40995b010f30a`" is the hash of
  the pivot LIST, not the file — it matches the extracted
  `sha256(repr(piv))[:16]` exactly, as does the C hash
  `6cffa0100555b7b8`. Extraction used a restricted unpickler
  (builtins + numpy ndarray/dtype only); exit 0.

### Phase 4.13 — C1(c): E7 eliminations carried, not re-verified

- The three elimination sub-cases inside E7 (Prop 4.3) — (a)/(b) by
  branches-(a),(b) `main_theorem`, (c) by `branch_c_eliminated` (both
  kernel, permitted triple) — are **carried from the prior GradeA
  verification (commit 7e4db07f) and were NOT re-verified by this
  gate** (G1 condition C1(c)). They are the only fully-kernel claims
  in the paper's numbered environments, and they do not make any
  numbered environment unconditional: `prop43_conditional` itself
  stays CONDITIONAL on its named `Prop43Premises`.

### Phase 4.14 — Verification logs filed (`lean/logs/`, 52 files)

Per-file FULL + AXIOMS logs as filed by the legs, plus leg running
logs and second-tool drivers. Sizes + SHA-256 (first 16 hex):

| File | Bytes | sha256 |
|---|---|---|
| `assembly_axioms.log` | 36,472 | `9381941a5e3adb88` |
| `assembly_full.log` | 36,472 | `9381941a5e3adb88` |
| `assembly_log.md` | 7,574 | `da4c80ffa339dee8` |
| `check_legA_2026-11-06.py` | 2,913 | `effa000f461cfe20` |
| `check_s4_second_tool.py` | 4,326 | `2deb647ade7fc889` |
| `gghv_full_721_coeff_2026-11-06_axioms.log` | 1,140 | `e7f00a87a4da3e59` |
| `gghv_full_721_coeff_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_central_gaps_2026-11-06_axioms.log` | 915 | `361757ffcf211f77` |
| `gghv_full_central_gaps_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_d1_theory_2026-11-06_axioms.log` | 1,651 | `c2f5ecdf805ec8b0` |
| `gghv_full_d1_theory_2026-11-06_full.log` | 1,185 | `b1b94af18cdd2652` |
| `gghv_full_d2_poly_2026-11-06_axioms.log` | 3,707 | `efa336ecbb1e3b1c` |
| `gghv_full_d2_poly_2026-11-06_full.log` | 2,893 | `5e6fb81f11959662` |
| `gghv_full_esquina3l_2026-11-06_axioms.log` | 1,249 | `7acb3c769997b33d` |
| `gghv_full_esquina3l_2026-11-06_full.log` | 802 | `c92df456d8a099b4` |
| `gghv_full_esquina_combined_2026-11-06_axioms.log` | 889 | `4af9920a14b8c4ee` |
| `gghv_full_esquina_combined_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_ggv1_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_ggvstar_2026-11-06_run2.axioms.txt` | 2,518 | `781bfd8b759a8261` |
| `gghv_full_ggvstar_ggv1_2026-11-06_run2.axioms.txt` | 3,376 | `6ccdc29df38c638b` |
| `gghv_full_ggvstar_ggv6_ggv5_2026-11-06_run2.axioms.txt` | 2,556 | `976244be31bd1802` |
| `gghv_full_hybrid_slip_2026-11-06_axioms.log` | 1,066 | `4ec297007a9eb13d` |
| `gghv_full_hybrid_slip_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_mayores_2026-11-06_axioms.log` | 1,069 | `7acb4df2f7863738` |
| `gghv_full_mayores_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_mn_gt1_2026-11-06_axioms.log` | 857 | `cb7eefbeca86ec62` |
| `gghv_full_mn_gt1_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `gghv_full_remark_facelaws_2026-11-06_axioms.log` | 973 | `62868a9b8106abd0` |
| `gghv_full_remark_facelaws_2026-11-06_full.log` | 602 | `cde36bb7cf253897` |
| `laurent_err.txt` | 16,817 | `f41a7e2548b9c6b6` |
| `laurent_log.md` | 19,264 | `e9a79e4ac617daeb` |
| `laurent_recursion_check.py` | 848 | `0a9e3218bbb6edfc` |
| `legA_axioms.log` | 1,539 | `a95e5d358f4ca56f` |
| `legA_full.log` | 344 | `d830ded753795637` |
| `legA_log.md` | 4,967 | `820d7079720fffa4` |
| `legB_log.md` | 10,540 | `4e6dfbbd17e8ef5e` |
| `legC_log.md` | 3,897 | `06f6c251e84a6986` |
| `legD.log` | 12,036 | `c67ea1b555ecf15d` |
| `legE_log.md` | 9,272 | `db286488cc7adc78` |
| `legF_gghv_full_ggvstar_2026-11-06_run2.log` | 23,208 | `578c1fde9a58ed23` |
| `legF_gghv_full_ggvstar_ggv1_2026-11-06_run2.log` | 21,874 | `839eb5d5584f8243` |
| `legF_gghv_full_ggvstar_ggv6_ggv5_2026-11-06_run2.log` | 22,435 | `757fdb2d9a53b23f` |
| `legF_log.md` | 33,355 | `a460f34235330853` |
| `r8_axioms.log` | 1,088 | `34dd6f7c4b782adc` |
| `s5_axioms.log` | 36,509 | `6044504dfcaf057a` |
| `s5_build_5.log` | 33,284 | `1d488386449a71c9` |
| `s6_axioms3.log` | 27,774 | `b1cf2cd801c75962` |
| `s6_full6.log` | 21,784 | `7ebfc2b1dc231801` |
| `second_tool.log` | 5,547 | `b22b4547178866b6` |
| `second_tool_checks.py` | 4,612 | `df6d3e072cfed1db` |
| `verify_all_stdout.log` | 21,948 | `e25e009a6d4fb537` |
| `verify_all_stdout2.log` | 14,045 | `487e87391a2b10a2` |
| `verify_legE.sh` | 5,982 | `e3e1e5b428a3249b` |

Notes: `assembly_full.log` and `assembly_axioms.log` share a SHA-256
because the same file (including its `#print axioms` block) was
compiled twice. Several Leg E FULL logs share a SHA-256 (602-byte
identical clean-compile records). Leg B produced no separate
FULL/AXIOMS log files — `legB_log.md` is its verification record.
Leg F round-5 logs are the `run2` files; earlier rounds are superseded
(see exclusions). Leg C `s5_build_5.log` is the final build log;
`s5_build_1..4.log` are superseded. Leg D `s6_axioms3.log` is the
final axioms log; `s6_axioms.log` / `s6_axioms2.log` are superseded.

### Phase 4.15 — Records filed (`gghv-dependency-closure/`)

| File | Bytes | sha256 |
|---|---|---|
| `gghv_full_assembly_inventory.md` | 73,680 | `3029d31641e699e1` |
| `validation_g1/g1_validation_report_2026-11-07.md` | 25,648 | `7eef4fddc04bd76e` |

The inventory is the definitive per-item verdict record (1,117
lines, G1 corrections F1/F2/F3 applied — verified by grep at filing).
The G1 report is the independent deepest-research fact-check:
CONDITIONAL GO, subject to C1 (this manifest), C2 (F1), C3 (F2),
C4 (F3). No claim FAILED outright.

### Phase 4.16 — What is NOT filed (Phase 4 exclusions, with reasons)

- **All `probe*.lean` files** (Legs B/C/D/E, Laurent) — scratch
  probes; stay in `~/workspace/research/tooling/`. Their results are
  in the filed leg files and logs.
- **Leg F section files** (`legF1_section_N/O`, `legF2a_section_P/Q/R`,
  `legF2b_section_S/T/U`) and `gen_legF*.py`, `run_legF_verify.sh` —
  assembly inputs / generators / drivers; the three filed Leg F files
  are the verified wholes.
- **Assembly inputs** (`assembly_section.lean`,
  `legA_body.lean`, `legB_body.lean`, `legC_body.lean`,
  `assembly_header.txt`) — intermediate inputs; the filed assembly
  file is self-contained.
- **Leg F round 1–4 logs** (`logs/run1.*`, `logs/round2/`,
  `logs/round3/`, `logs/round4/`) — superseded verification rounds;
  round 5 (run2) is the final clean pass.
- **Leg C `s5_build_1..4.log`** — superseded build rounds;
  `s5_build_5.log` is final.
- **Leg D `s6_axioms.log`, `s6_axioms2.log`** — superseded axioms
  runs; `s6_axioms3.log` is final. `s6_certificate_generated.lean`
  + `gen_certificate.py` — intermediate generator output; the
  certificate identity is transcribed and re-verified inside the
  filed Leg D file and the Singular logs.
- **Leg E `probe_api_2026-11-06_full.log`** — probe log, superseded by
  the filed per-file logs. `rerun_r13_axioms.sh` — scratch rerun
  helper; the rerun is recorded in the filed logs.
- **Leg B `probe_s4_2026-11-06.lean`** — probe; the parse bug it found
  is fixed in the filed file.
- **Leg H `vm_out` intermediate pkls** — the 79 MB `INVERSE.pkl` is
  already tracked in this repo (see §4.12) and is never copied as a
  new blob; `inv_work_M.pkl` and the extracted 81.8 MB `C.npy` (deleted
  after the det(C) cross-check) are not filed.
- **Retrieval leg files** (`retrieval_log.md`,
  `arxiv_tex_numbering_note.md`) — not filed in this commit; the
  retrieval outcome (published [GGV1] §7 text and Joseph Lemma 2.2
  NOT FOUND) is recorded in the inventory.

### Phase 4.17 — Scope guard (Phase 4)

Nothing in Phase 4 proves JC(2), proves Theorem R, or excludes
(72, 108) unconditionally. Theorem R is excluded from this programme
everywhere. The E7 eliminations are the only fully-kernel claims among
the paper's numbered environments, and they are carried from commit
7e4db07f (see §4.13), not re-verified by gate G1.
