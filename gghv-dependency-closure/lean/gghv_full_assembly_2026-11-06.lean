import Mathlib

/-!
# GGHV full-proof assembly (Phase 4, scratch) — Theorem 2.1 with Leg B/C
# refined fields 9–10

**CLAIM:** `theorem21_minimal_v2` reproves Leg A's Theorem 2.1 from a
refined 20-field premise list (`MinimalPremises2`) in which Leg A's opaque
links `link_924` / `link_927` are replaced by named chains built from the
verified Leg B (§4, vertex-level reductions) and Leg C (§5, Theorem 5.1
endgame) conditional theorems. The composition is kernel: the links are
*derived* (`link_924_derived`, `link_927_derived`), not assumed.
**STATUS:** Scratch assembly — NO repo commits; incorporation only after
the validation gate. Lean 4.34.0 / Lake 5.0.0, `import Mathlib` only,
self-contained (Leg A + Leg B + Leg C contents copied in verbatim below;
no leg file is imported). No `sorry`, no `axiom` declarations, no `admit`.

## What is copied in, and where it came from (verbatim, unmodified except
## for the stripped duplicate `import Mathlib` lines)

- Leg A: `~/workspace/research/tooling/phase4_legA/gghv_full_s2s3_2026-11-06.lean`
  (645 lines; FULL_EXIT=0, 6 s; 21 theorems, axioms per `legA_axioms.log`).
  Supplies the §2 table, the red rows, the §3-84/§3-120 kernel arithmetic,
  `discard_924_row` / `discard_927_row`, and `theorem21_minimal`.
- Leg B: `~/workspace/research/tooling/phase4_legB/gghv_full_s4_2026-11-06.lean`
  (1,378 lines; FULL_EXIT=0, 7–8 s; `prop41_conditional` [propext,
  Quot.sound], `prop42_conditional` [triple], `prop43_conditional`
  [propext, Quot.sound], `prop44_conditional` [triple]).
  Supplies the §4 vertex-level reductions and the E9 algorithm.
- Leg C: `~/workspace/research/tooling/phase4_legC/gghv_full_s5_2026-11-06.lean`
  (836 lines; FULL_EXIT=0, 42 s; `thm51_conditional` [triple],
  `cor52_conditional` [no axioms]). Supplies E13 (kernel), the E16
  certificate/elimination, E14/E15 conditional bounds, E12/E11 kernel
  pieces, and the E10/E17 conditional assemblies.

## What the assembly section adds (at the end of this file)

`Prop42Shape` / `Prop41Shape` (the pure reduced shapes),
`prop42_shape_of` / `prop41_shape_of` (kernel extraction),
`S5Link` (Leg C's §5 data-link type), `MinimalPremises2` (20 fields),
`link_924_derived` / `link_927_derived` (the old opaque links, proved
from the refined chains), `theorem21_minimal_v2` /
`theorem21_conditional_minimal_v2`. See the assembly-section header for
the honest discharge audit: fields 9–10 are REFINED, not unconditionally
discharged — the bridge (polynomial lift + Cor 5.7 step) and the §5 data
links remain carried, now with precise names.

## Verification record (filled by the assembly run; see `assembly_log.md`)

- FULL run: (to be filled: exit code, seconds, error count)
- AXIOMS run: (to be filled: exit code, per-theorem axiom lists)
-/


/-!
# Leg A — GGHV §2/§3 + Theorem 2.1 (Phase 4 full-proof programme, scratch)

**CLAIM:** The §2 table as a single bundled theorem (all 10 rows, bound < 125,
survivors filter, degree-pair provenance); the §3-120 and §3-84 discard
arguments with every in-paper arithmetic step proved by the kernel and the
cited external results carried as EXPLICIT named premises; Theorem 2.1 from
the 11-field minimal premise list (conditional).
**STATUS:** KERNEL where stated below; CONDITIONAL where a named premise is
carried; NO `theorem21_unconditional` is claimed.

## What is new here vs Phase 1 (`d1_assembly_2026-11-05.lean`, `d1_ggvstar`)

- E2 table: one bundled theorem `gghv_table_full` (rows + degree pairs + max
  degrees + bound + survivors + red-row membership); survivor-pair uniqueness
  (`pair_108_72_unique`, `pair_72_108_unique`); survivors as rows, not just
  degree pairs (`survivors_exact`).
- E3 (§3-120): NEW kernel steps — the direction equality
  `v_{4,-1}(A_1) = v_{4,-1}(A_2)` (`v_120_direction`, in ℚ); uniqueness of the
  end point (`v_120_en_unique`: `4μ = 3 → μ = 3/4`); the `d₀` bound
  (`d0_bound`: `d·(2,7) = (8,28) → d = 4`; `d0_forced_4`: `4 ∣ d₀ ∧ d₀ ≤ 4
  → d₀ = 4`); the transformed-corner exponents (`corner_120_exponents`:
  `2·(4m) = 8m`, `1·(4m) = 4m`); all packaged in `discard_120_kernel_data`.
  What is NOT proved (carried): [GGV1] Thm 7.6(5) (numbering UNRESOLVED;
  retrieval leg: published §7 text NOT FOUND, 15 routes exhausted — the
  arXiv TeX numbering note is not the published text); [GGV2] Prop 3.29
  (carried as universal `prop329` over abstract `LPC`); [GGV2] Remark 3.31;
  the last-possible-corner computation `link_120` (Leg F, not landed).
- E4 (§3-84): NEW kernel steps in ℚ, faithful to the paper's fractions —
  `im_84_general` (`I_M(j) = 2(j+2)` for every `j`); `im_84_at_j0` (`= 4`);
  `im_minor_84_rat` (`1 - (-3+1) - 7·(-9/7+1) = 5`); the minor-δ step
  (`minor_delta_step`: `-9/7 + 1 = -2/7`); the factor count
  (`factor_count_84`: `7 + 7 = 14`, `(2+1)·7 = 21`); packaged in
  `discard_84_kernel_data`. Int versions kept for the assembly
  (`im_minor_84`, `discard_84_numeric`). What is NOT proved (carried):
  [GGV6] Thm 7.3 (the inequality `I_M ≥ I_m`, carried as the link
  hypothesis); [GGV1] Prop 2.11(3); [GGV6] Props 6.4/6.6 and Ex 6.7;
  the π-root machinery and the `τ = -x + λ₀ + λ₋₂x⁻² + πx⁻³` verification
  (Leg F, not landed).
- E2 red rows: NOT proved — the cited arguments live in [GGV4] §3.5, [M],
  [H] (rows 1–2), [GGV3] §5 (rows 3–4), [GGV5] Prop 6.1 (row 6). The local
  [GGV5] TeX (1708.07936, §6 = "Program and graphic display") does not
  contain a Proposition 6.1 under that number, and formalising any of these
  discards needs the cited papers' Newton-polygon machinery (regular corners,
  complete chains) — that is Leg F's R20, not landed. Each red row is
  therefore carried as ONE explicit named field of `RedRowPremises`, and
  `red_rows_eliminated` proves the five row eliminations CONDITIONALLY on
  those fields. Nothing here claims a red row is unconditionally discarded.
- E2 table completeness: NOT PROVED and NOT provable from the table data —
  it is the statement `TableCompleteness` (every counterexample with
  max < 125 has its shape among the 10 rows), i.e. [GGV5] §§5–6 enumeration
  completeness, Leg F's R19. It is carried as field 11 of `MinimalPremises`.
  What blocks it, precisely: the generative side of the [GGV5] enumeration
  (family generation from admissible complete chains + proof that no chain
  outside the 10 rows exists below max 125). The first-stage PLLC filter
  alone (Phase 1, recomputed I1) does not give completeness.
- E1 (Theorem 2.1): `theorem21_minimal` reproved here from the 11-field
  `MinimalPremises`. Of the 11 fields, NONE is discharged in this leg:
  fields 1–5 are the red rows (above); field 6 is the §3-84 link (Leg F);
  fields 7–8 are Prop 3.29 + the LPC computation (Leg F); fields 9–10 are
  the §4 reductions + §5 elimination links (Legs B/C, not landed — leg dirs
  empty at time of writing; the §4 links also inherit the hybrid-vs-slip
  question for the swapped Cor 7.4 uses, which stays carried now that the
  retrieval leg has closed with published §7 NOT FOUND); field 11 is
  enumeration completeness (Leg F). The §6 route for the (7,21) row is NOT
  on the minimal list: the §3 route already eliminates that row
  (`discard_721_via_sec3`).
- `sorryAx` NOWHERE in this file. Axiom lists are recorded from `#print
  axioms` in the leg log.

## Abstract predicates (parameters of this file, as in Phase 1)

`CounterexampleAt : CaseRow → Prop` (a counterexample with the given Newton
shape), `Counterexample : Nat → Nat → Prop` (a counterexample with the given
degree pair), `LPC : Nat × Nat → Prop` ([GGV2] Def. 3.21, last possible
corner). No claim is made about their definitions.
-/

/-! ### Section 1 — The §2 table (E2): rows, degree pairs, bound, survivors -/

/-- A row of the GGHV §2 table: A₀, the (m, n) pair, and the paper's stated max degree. -/
structure CaseRow where
  a0 : Nat × Nat
  m : Nat
  n : Nat
  maxDeg : Nat
deriving DecidableEq, Repr

/-- The degree pair of a row, by the [GGV5] family formula. -/
def degreePair (r : CaseRow) : Nat × Nat :=
  (r.m * (r.a0.1 + r.a0.2), r.n * (r.a0.1 + r.a0.2))

/-- The max degree of a row's degree pair. -/
def pairMax (r : CaseRow) : Nat :=
  max (degreePair r).1 (degreePair r).2

/-- The ten rows of the GGHV §2 table, in the paper's order. -/
def table : List CaseRow :=
  [ ⟨(4, 12), 3, 4, 64⟩,
    ⟨(4, 12), 5, 7, 112⟩,
    ⟨(5, 20), 2, 3, 75⟩,
    ⟨(5, 20), 3, 2, 75⟩,
    ⟨(7, 21), 2, 3, 84⟩,
    ⟨(8, 24), 2, 3, 96⟩,
    ⟨(8, 28), 3, 2, 108⟩,
    ⟨(8, 32), 3, 2, 120⟩,
    ⟨(9, 24), 2, 3, 99⟩,
    ⟨(9, 27), 2, 3, 108⟩ ]

/-- The (8,28) row: the only row left after all discards. -/
def row828 : CaseRow := ⟨(8, 28), 3, 2, 108⟩

theorem row828_in_table : row828 ∈ table := by decide

theorem row828_degree_pair : degreePair row828 = (108, 72) := by rfl

/-- P↔Q swap of a degree pair. -/
def swapPair (p : Nat × Nat) : Nat × Nat := (p.2, p.1)

theorem row828_swap : swapPair (degreePair row828) = (72, 108) := by rfl

/-- Every row's degree pair has the paper's stated max degree. -/
theorem table_max_degrees :
    table.map pairMax = [64, 112, 75, 75, 84, 96, 108, 120, 99, 108] := by
  rfl

/-- Every row's degree pair, in table order. -/
theorem table_degree_pairs :
    table.map degreePair =
      [(48, 64), (80, 112), (50, 75), (75, 50), (56, 84),
       (64, 96), (108, 72), (120, 80), (66, 99), (72, 108)] := by
  rfl

/-- The table really is a list of cases with max degree < 125, as §2 assumes. -/
theorem table_below_125 : ∀ r ∈ table, r.maxDeg < 125 := by
  decide

/-- The (72,108) case: gcd and reduced ratio. -/
theorem deg_72_108_gcd : Nat.gcd 72 108 = 36 := by rfl

theorem deg_72_108_ratio : (72 / Nat.gcd 72 108, 108 / Nat.gcd 72 108) = (2, 3) := by
  rfl

/-- The (72,108) row is in the table: the (9,27) row. -/
theorem row_72_108_in_table : (⟨(9, 27), 2, 3, 108⟩ : CaseRow) ∈ table := by
  decide

/-- The (108,72) row is in the table: the (8,28) row. -/
theorem row_108_72_in_table : (⟨(8, 28), 3, 2, 108⟩ : CaseRow) ∈ table := by
  decide

/-- The §2 table as ONE bundled theorem: all 10 rows, their degree pairs,
    their max degrees, the < 125 bound, and the 10-row count. -/
theorem gghv_table_full :
    table.length = 10 ∧
    table.map degreePair =
      [(48, 64), (80, 112), (50, 75), (75, 50), (56, 84),
       (64, 96), (108, 72), (120, 80), (66, 99), (72, 108)] ∧
    table.map pairMax = [64, 112, 75, 75, 84, 96, 108, 120, 99, 108] ∧
    (∀ r ∈ table, r.maxDeg < 125) ∧
    (∀ r ∈ table, pairMax r = r.maxDeg) := by
  refine ⟨by decide, by rfl, by rfl, by decide, by decide⟩

/-- Ten-way case split on a table row. -/
theorem table_cases (r : CaseRow) (h : r ∈ table) :
    r = ⟨(4, 12), 3, 4, 64⟩ ∨ r = ⟨(4, 12), 5, 7, 112⟩ ∨
    r = ⟨(5, 20), 2, 3, 75⟩ ∨ r = ⟨(5, 20), 3, 2, 75⟩ ∨
    r = ⟨(7, 21), 2, 3, 84⟩ ∨ r = ⟨(8, 24), 2, 3, 96⟩ ∨
    r = ⟨(8, 28), 3, 2, 108⟩ ∨ r = ⟨(8, 32), 3, 2, 120⟩ ∨
    r = ⟨(9, 24), 2, 3, 99⟩ ∨ r = ⟨(9, 27), 2, 3, 108⟩ := by
  simp only [table, List.mem_cons, List.mem_nil_iff, or_false] at h
  exact h

/-! ### Section 2 — The red rows (E2): carried premises + conditional eliminations -/

/-- The five rows the paper marks red (discarded by cited papers). -/
def redRows : List CaseRow :=
  [ ⟨(4, 12), 3, 4, 64⟩,
    ⟨(4, 12), 5, 7, 112⟩,
    ⟨(5, 20), 2, 3, 75⟩,
    ⟨(5, 20), 3, 2, 75⟩,
    ⟨(8, 24), 2, 3, 96⟩ ]

theorem redRows_length : redRows.length = 5 := by rfl

theorem redRows_in_table : ∀ r ∈ redRows, r ∈ table := by
  decide

variable (CounterexampleAt : CaseRow → Prop) (Counterexample : Nat → Nat → Prop)
  (LPC : Nat × Nat → Prop)

/-- The five red-row discards, as EXPLICIT named premises with their citations.
    Each field is one cited theorem, not formalised here (see the file header):
    [GGV4] §3.5 + [M] + [H] for (4,12)/(3,4); [GGV4] §3.5 for (4,12)/(5,7);
    [GGV3] §5 for the two (5,20) rows; [GGV5] Prop 6.1 for (8,24)/(2,3). -/
structure RedRowPremises where
  red_412_34 : ¬ CounterexampleAt ⟨(4, 12), 3, 4, 64⟩
  red_412_57 : ¬ CounterexampleAt ⟨(4, 12), 5, 7, 112⟩
  red_520_23 : ¬ CounterexampleAt ⟨(5, 20), 2, 3, 75⟩
  red_520_32 : ¬ CounterexampleAt ⟨(5, 20), 3, 2, 75⟩
  red_824_23 : ¬ CounterexampleAt ⟨(8, 24), 2, 3, 96⟩

/-- Every red row is eliminated, CONDITIONALLY on the five cited theorems. -/
theorem red_rows_eliminated (h : RedRowPremises CounterexampleAt) :
    (∀ r ∈ redRows, ¬ CounterexampleAt r) := by
  intro r hr
  simp only [redRows, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.red_412_34
  · exact h.red_412_57
  · exact h.red_520_23
  · exact h.red_520_32
  · exact h.red_824_23

/-- Rows remaining after the red discards, as degree pairs. -/
theorem remaining_after_red :
    (table.filter (fun r => r ∉ redRows)).map degreePair =
      [(56, 84), (108, 72), (120, 80), (66, 99), (72, 108)] := by
  rfl

/-- The survivors as ROWS (not just degree pairs): after removing the five red
    rows and the max = 84 and max = 120 rows, exactly the (8,28), (9,24) and
    (9,27) rows remain. -/
theorem survivors_exact :
    (table.filter (fun r => r ∉ redRows ∧ r.maxDeg ≠ 84 ∧ r.maxDeg ≠ 120)) =
      [⟨(8, 28), 3, 2, 108⟩, ⟨(9, 24), 2, 3, 99⟩, ⟨(9, 27), 2, 3, 108⟩] := by
  decide

/-- Rows surviving the paper's §2/§3 discards, as degree pairs. -/
theorem section2_survivors :
    ((table.filter (fun r => r.maxDeg ≠ 84 ∧ r.maxDeg ≠ 120)).map degreePair).filter
      (fun p => p ≠ (48, 64) ∧ p ≠ (80, 112) ∧ p ≠ (50, 75) ∧ p ≠ (75, 50) ∧
        p ≠ (64, 96)) = [(108, 72), (66, 99), (72, 108)] := by
  rfl

/-- The (108,72) degree pair comes from exactly one table row, the (8,28) row. -/
theorem pair_108_72_unique :
    ∀ r ∈ table, degreePair r = (108, 72) → r = ⟨(8, 28), 3, 2, 108⟩ := by
  decide

/-- The (72,108) degree pair comes from exactly one table row, the (9,27) row
    (the (8,28) row gives (72,108) only after the P↔Q swap). -/
theorem pair_72_108_unique :
    ∀ r ∈ table, degreePair r = (72, 108) → r = ⟨(9, 27), 2, 3, 108⟩ := by
  decide

/-- The (72,108) pair from the (9,27) row, directly. -/
theorem pair_72_108_from_927 : (2 * (9 + 27), 3 * (9 + 27)) = (72, 108) := by
  decide

/-- The (72,108) pair from the (8,28) row, swapped. This is why eliminating
    the (9,27) ROW does not eliminate the degree PAIR (72,108) — the
    row-vs-degree-pair correction, now computed. -/
theorem pair_72_108_from_828_swapped : (2 * (8 + 28), 3 * (8 + 28)) = (72, 108) := by
  decide

/-! ### Section 3 — The §3-120 discard (E3): kernel arithmetic + carried premises -/

/-- §3, max = 120 case: the data the paper computes.
    A₀ = (8,32), A₁ = (8,28), A₂ = (11/4, 7), direction (ρ₁, σ₁) = (4, -1). -/
def corner_120_a0 : Nat × Nat := (8, 32)
def corner_120_a1 : Nat × Nat := (8, 28)

/-- The direction computation: `v_{4,-1}(A_1) = v_{4,-1}(A_2)`, i.e.
    `4·8 + (-1)·28 = 4·(11/4) + (-1)·7 = 4`. Hence `(ρ₁,σ₁) = (4,-1)`. -/
theorem v_120_direction :
    (4 : ℚ) * 8 + (-1) * 28 = (4 : ℚ) * (11 / 4) + (-1) * 7 := by
  norm_num

/-- `en_{4,-1}(F_1) = (6,21)` is the ONLY point of the form `μ(8,28)` with
    `v_{4,-1} = 3`: `v_{4,-1}(μ(8,28)) = 4μ`, so `4μ = 3` forces `μ = 3/4`. -/
theorem v_120_en_unique (μ : ℚ)
    (h : (4 : ℚ) * (μ * 8) + (-1) * (μ * 28) = 3) : μ = 3 / 4 := by
  linarith

/-- `en_{4,-1}(F_1) = (6,21) = (3/4)·(8,28)`, cross-multiplied. -/
theorem discard_120_data :
    (6 * 4 = 3 * 8 ∧ 21 * 4 = 3 * 28) := by
  decide

/-- `q_1 = 4`, from [GGV1] Thm 7.6(5): `q_1 = 4 | d₀` with `d₀ ≤ 4`, and
    `st_{1,0}(P) = (8,28) = 4·(2,7)` with `gcd(2,7) = 1`. -/
theorem discard_120_gcd : Nat.gcd 2 7 = 1 := by rfl

/-- The `d₀ ≤ 4` step, as pure arithmetic: if `d·(2,7) = (8,28)`
    componentwise then `d = 4`. -/
theorem d0_bound (d : Nat) (h1 : d * 2 = 8) (h2 : d * 7 = 28) : d = 4 := by
  omega

/-- The divisibility step: `4 ∣ d₀` and `d₀ ≤ 4` (with `d₀ > 0`) force `d₀ = 4`. -/
theorem d0_forced_4 (d0 : Nat) (hdvd : 4 ∣ d0) (hle : d0 ≤ 4) (hpos : 0 < d0) :
    d0 = 4 := by
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- The transformed corner after `φ(x) = x`, `φ(y) = y + λ₁`: from
    `ℓ_{1,0}(φ(P)) = (λ_P x² y (y + λ₁)⁷)^{4m}` the lowest `x`-exponent is
    `2·(4m) = 8m` and the lowest `y`-exponent is `1·(4m) = 4m`, i.e. scaled
    by `1/m` the corner is `A₀' = (8,4)`. -/
theorem corner_120_exponents (m : Nat) :
    2 * (4 * m) = 8 * m ∧ 1 * (4 * m) = 4 * m := by
  constructor <;> ring

/-- The transformed corner `A₀' = (8,4)`. -/
def corner_120_transformed : Nat × Nat := (8, 4)

theorem corner_120_transformed_eq : corner_120_transformed = (8, 4) := by
  rfl

/-- [GGV2] Prop 3.29 ("casos imposibles"), applied to (8,4): a last possible
    corner (a,b) must satisfy `b + gcd(a,b) ≠ a`; but `4 + gcd(8,4) = 8 = a`.
    This arithmetic is KERNEL; the proposition itself is carried as the
    hypothesis `h329` below. -/
theorem prop329_exclusion_84 : 4 + Nat.gcd 8 4 = 8 := by decide

/-- All §3-120 kernel arithmetic in one bundle. -/
theorem discard_120_kernel_data :
    ((4 : ℚ) * 8 + (-1) * 28 = (4 : ℚ) * (11 / 4) + (-1) * 7) ∧
    (6 * 4 = 3 * 8 ∧ 21 * 4 = 3 * 28) ∧
    Nat.gcd 2 7 = 1 ∧
    (∀ d : Nat, d * 2 = 8 → d * 7 = 28 → d = 4) ∧
    (∀ m : Nat, 2 * (4 * m) = 8 * m ∧ 1 * (4 * m) = 4 * m) ∧
    (4 + Nat.gcd 8 4 = 8) :=
  ⟨v_120_direction, discard_120_data, discard_120_gcd, d0_bound,
    corner_120_exponents, prop329_exclusion_84⟩

/-- The §3-120 discard, as a row elimination. Two carried items: the general
    [GGV2] Prop 3.29 (as a universal statement over the abstract `LPC`
    predicate) and the link hypothesis `h120` (a row-120 counterexample would
    make (8,4) the last possible corner of φ(P)). Remaining gaps: the
    last-possible-corner computation (Leg F) + [GGV2] Prop 3.29 itself
    (Leg F) + [GGV1] Thm 7.6(5) numbering (retrieval: published §7 NOT FOUND). -/
theorem discard_120_row
    (h329 : ∀ (a b : Nat), LPC (a, b) → b + Nat.gcd a b ≠ a)
    (h120 : CounterexampleAt ⟨(8, 32), 3, 2, 120⟩ → LPC (8, 4)) :
    ¬ CounterexampleAt ⟨(8, 32), 3, 2, 120⟩ := by
  intro hc
  exact h329 8 4 (h120 hc) prop329_exclusion_84

/-! ### Section 4 — The §3-84 discard (E4): kernel arithmetic + carried premises -/

/-- §3, max = 84 case: family F₉ data. A₀ = (7,21), A₁ = (11/7, 2), k = 1,
    m = j + 2, n = 2j + 3. -/
def f9_m (j : Nat) : Nat := j + 2

theorem f9_m_at_j0 : f9_m 0 = 2 := by rfl

/-- `I_M = Σ |D|·λ = 7·(2m)·(1/7) = 2(j+2)`, for EVERY `j` (not just `j = 0`). -/
theorem im_84_general (j : Nat) :
    (7 : ℚ) * (2 * ((j : ℚ) + 2)) * (1 / 7) = 2 * ((j : ℚ) + 2) := by
  have h7 : (7 : ℚ) * (1 / 7) = 1 := by norm_num
  calc (7 : ℚ) * (2 * ((j : ℚ) + 2)) * (1 / 7)
      = (2 * ((j : ℚ) + 2)) * (7 * (1 / 7)) := by ring
    _ = 2 * ((j : ℚ) + 2) := by rw [h7, mul_one]

/-- At `j = 0` (the smallest case): `I_M = 4`. -/
theorem im_84_at_j0 : (7 : ℚ) * (2 * ((0 : ℚ) + 2)) * (1 / 7) = 4 := by
  norm_num

/-- The minor-δ step: each of the 7 minor roots has `δ = -9/7`, so
    `δ + 1 = -2/7`. -/
theorem minor_delta_step : (-9 / 7 : ℚ) + 1 = -2 / 7 := by
  norm_num

/-- The paper's `I_m` formula, in ℚ arithmetic (faithful to the fractions):
    one final minor π-root with `δ = -3` gives `δ + 1 = -2`; the 7 minor
    roots contribute `7·(-2/7) = -2`. Hence `I_m = 1 - (-2) - (-2) = 5`. -/
theorem im_minor_84_rat :
    (1 : ℚ) - (-3 + 1) - 7 * (-9 / 7 + 1) = 5 := by
  norm_num

/-- The factor count: `ℓ_{7,-2}(P) = ((z⁷-α₁)²(z⁷-α₂))^m` has `7 + 7 = 14`
    different factors (7 major + 7 minor), of total degree `(2+1)·7 = 21`
    per factor of `m`. -/
theorem factor_count_84 : (7 + 7 = 14 ∧ (2 + 1) * 7 = 21) := by
  decide

/-- The Int versions (for the assembly): the paper's `I_m` formula and the
    numeric contradiction `I_M = 4 < 5 = I_m`. -/
theorem im_minor_84 :
    (1 : Int) - (-2) - (7 * (-2) / 7) = 5 := by decide

theorem discard_84_numeric : (4 : Int) < 5 := by decide

/-- The ℚ numeric contradiction at the heart of the §3-84 discard. -/
theorem discard_84_numeric_rat : (4 : ℚ) < 5 := by norm_num

/-- All §3-84 kernel arithmetic in one bundle. -/
theorem discard_84_kernel_data :
    ((∀ j : Nat, (7 : ℚ) * (2 * ((j : ℚ) + 2)) * (1 / 7) = 2 * ((j : ℚ) + 2))) ∧
    ((7 : ℚ) * (2 * ((0 : ℚ) + 2)) * (1 / 7) = 4) ∧
    ((1 : ℚ) - (-3 + 1) - 7 * (-9 / 7 + 1) = 5) ∧
    ((4 : ℚ) < 5) ∧
    (7 + 7 = 14 ∧ (2 + 1) * 7 = 21) :=
  ⟨im_84_general, im_84_at_j0, im_minor_84_rat, discard_84_numeric_rat,
    factor_count_84⟩

/-- `I_M = I(P,Q)` and `I_m ≤ I(P,Q)` combine to `I_m ≤ I_M` ([GGV6] Thm 7.3),
    as a carried bundle: the two theorems are [GGV6]'s; only the combination
    is proved here. -/
structure IntersectionFormulas where
  IM : Int
  Im : Int
  IPQ : Int
  hM : IM = IPQ
  hm : Im ≤ IPQ

theorem im_le_IM (F : IntersectionFormulas) : F.Im ≤ F.IM := by
  rw [F.hM]
  exact F.hm

/-- The §3-84 discard, in conditional form: it takes [GGV6] Thm 7.3
    (`I_M ≥ I_m`) and the computed values as hypotheses. -/
theorem discard_84_conditional (IM IMm : Int) (h73 : IM ≥ IMm)
    (hIM : IM = 4) (hIm : IMm = 5) : False := by
  rw [hIM, hIm] at h73
  exact absurd h73 (by decide : ¬ (4 : Int) ≥ 5)

/-- The §3-84 discard, as a row elimination. The link hypothesis `h84` is the
    precise remaining premise: a counterexample at the (7,21) row has
    intersection numbers satisfying `I_M ≥ I_m` with values 4 and 5. Its
    justification is [GGV6] Thm 7.3 (the inequality) + GGHV §3's F₉-family
    computation (the values, proved above). The remaining gap is exactly:
    formalise [GGV6]'s π-root machinery and apply Thm 7.3 to the F₉ family
    (Leg F). -/
theorem discard_84_row
    (h84 : CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ →
      ∃ (IM Im : Int), IM ≥ Im ∧ IM = 4 ∧ Im = 5) :
    ¬ CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ := by
  intro hc
  obtain ⟨IM, Im, hge, h4, h5⟩ := h84 hc
  exact discard_84_conditional IM Im hge h4 h5

/-- The (7,21) row via §6 is the SAME row: `⟨(7,21), 2, 3, 84⟩` is both the
    max=84 row and the §6 row. So the §3 route already eliminates it, and the
    §6 route is not needed for Theorem 2.1. -/
theorem discard_721_via_sec3
    (h84 : CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ →
      ∃ (IM Im : Int), IM ≥ Im ∧ IM = 4 ∧ Im = 5) :
    ¬ CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ :=
  discard_84_row CounterexampleAt h84

/-! ### Section 5 — The §5 discards: (9,24) and (9,27) (E10, kernel endgame only) -/

/-- §5 Theorem ("teorema impossible", TeX 1402) conditions, as data. -/
def thm5_en_P : Nat × Nat := (6, 16)
def thm5_en_Q : Nat × Nat := (9, 24)
def thm5_st_P : Nat × Nat := (6, 18)
def thm5_st_Q : Nat × Nat := (9, 27)

/-- §5 degree bounds from the paper's endgame, kernel-checked:
    `12 + 9·7 = 75` and `22 + 8 + 42 + 4 = 76`. -/
theorem thm5_bounds : (12 + 9 * 7 = 75 ∧ 22 + 8 + 42 + 4 = 76) := by
  decide

/-- §5: `deg((y+1)^66 g(y)^3) = 78` forces `deg g = 4`, since `66 + 3·4 = 78`. -/
theorem thm5_g_degree : 66 + 3 * 4 = 78 := by rfl

/-- §5 endgame, conditionally: if the principal equation equates a degree-78
    term with terms bounded by 75 and 76, that is impossible. -/
theorem thm5_endgame (h78 : Nat) (h_bound : h78 ≤ 76) (h_eq : h78 = 78) :
    False := by
  rw [h_eq] at h_bound
  exact absurd h_bound (by decide : ¬ (78 : Nat) ≤ 76)

/-- The (9,24) discard, as a row elimination. The link hypothesis `h924` is
    the precise remaining premise: a counterexample at the (9,24) row, after
    the Prop 4.2 reduction and the §5 elimination, yields the principal
    equation equating a degree-78 term with terms bounded by 76. Legs B/C
    have not landed (leg dirs empty at time of writing); the link is carried. -/
theorem discard_924_row
    (h924 : CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ →
      ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76) :
    ¬ CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ := by
  intro hc
  obtain ⟨h78, heq, hle⟩ := h924 hc
  exact thm5_endgame h78 hle heq

/-- The (9,27) discard, as a row elimination. Same §5 endgame; the link
    hypothesis `h927` differs from `h924` in the §4 reduction (Prop 4.1
    instead of 4.2) and in that Cor 5.7's Succ/ψ step is part of its
    justification. Legs B/C have not landed; the link is carried. -/
theorem discard_927_row
    (h927 : CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ →
      ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76) :
    ¬ CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ := by
  intro hc
  obtain ⟨h78, heq, hle⟩ := h927 hc
  exact thm5_endgame h78 hle heq

/-! ### Section 6 — The (7,21) row via §6: what is proved, what is NOT -/

/-- §6 Theorem ("teorema impossible para 7", TeX 1817) conditions, as data. -/
def thm6_P : List (Nat × Nat) := [(0, 0), (4, 0), (2, 6), (0, 14)]
def thm6_Q : List (Nat × Nat) := [(0, 0), (6, 0), (3, 9), (0, 21)]

/-- §6 principal equation degrees at `k = 2`: all three terms are 27.
    This degree check is KERNEL. -/
theorem thm6_principal_degrees_at_k2 :
    (15 + 6 * 2 = 27 ∧ 9 + 9 * 2 = 27) := by
  decide

/-- §6 scaling check (Part3's `thm721_scaling`, restated). -/
theorem thm721_scaling :
    (6 * 2 = 4 * 3 ∧ 3 * 2 = 2 * 3 ∧ 9 * 2 = 6 * 3 ∧ 0 * 2 = 0 * 3) := by
  decide

/-- The §6 route is NOT claimed here and NOT needed for Theorem 2.1
    (see `discard_721_via_sec3`). -/
theorem sec6_route_not_needed : True := by
  trivial

/-! ### Section 7 — Enumeration completeness: the exact open statement -/

/-- Table completeness, as a NAMED proposition: every counterexample with
    max degree < 125 has its shape among the 10 table rows. This is [GGV5]
    §§5–6 enumeration completeness (Leg F, R19) — NOT proved here, and not
    provable from the table arithmetic, which never mentions `Counterexample`.
    It is carried as field 11 of `MinimalPremises` below. -/
def TableCompleteness : Prop :=
  ∀ (degP degQ : Nat), Counterexample degP degQ →
    max degP degQ < 125 →
    ∃ r ∈ table, CounterexampleAt r ∧ degreePair r = (degP, degQ)

/-- The (5,20) A₀ occurs in exactly two rows of the table — GGHV's note that
    the max-75 case "corresponds to two cases in two different families" —
    so the §5 contribution is 7 rows, and `7 + 3 = 10` rows total. -/
def rowsA0 : List (Nat × Nat × Nat × Nat) :=
  [ (4, 12, 3, 4), (4, 12, 5, 7), (5, 20, 2, 3), (5, 20, 3, 2)
  , (7, 21, 2, 3), (8, 24, 2, 3), (8, 28, 3, 2), (8, 32, 3, 2)
  , (9, 24, 2, 3), (9, 27, 2, 3) ]

theorem rowsA0_length : rowsA0.length = 10 := by decide

theorem rowsA0_520_twice :
    (rowsA0.filter (fun r => r.1 = 5 && r.2.1 = 20)).length = 2 := by
  decide

theorem source_count : 7 + 3 = 10 := by decide

/-- Max degree from the family formula: `max(m,n)·(a+b)`. The computed max
    degree equals the table's in all 10 rows. -/
def rowMaxDeg (r : Nat × Nat × Nat × Nat × Nat) : Nat :=
  max r.2.2.1 r.2.2.2.1 * (r.1 + r.2.1)

def rows10 : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (4, 12, 3, 4, 64)
  , (4, 12, 5, 7, 112)
  , (5, 20, 2, 3, 75)
  , (5, 20, 3, 2, 75)
  , (7, 21, 2, 3, 84)
  , (8, 24, 2, 3, 96)
  , (8, 28, 3, 2, 108)
  , (8, 32, 3, 2, 120)
  , (9, 24, 2, 3, 99)
  , (9, 27, 2, 3, 108) ]

theorem rows10_max_degrees :
    rows10.all (fun r => rowMaxDeg r = r.2.2.2.2) = true := by decide

/-! ### Section 8 — The assembly: minimal premises + Theorem 2.1 (E1) -/

/-- The MINIMAL remaining premise list for Theorem 2.1 (11 fields).
    Fields 1–5 are the five cited theorems for the red rows (EXTERNAL).
    Field 6 packages [GGV6] Thm 7.3 + the §3 computation. Field 7 is
    [GGV2] Prop 3.29 in universal form. Field 8 is the §3-120
    last-possible-corner computation. Fields 9–10 package the §4 reductions +
    the §5 elimination + the bounds (+ Cor 5.7's step for field 10). Field 11
    is [GGV5] enumeration completeness (`TableCompleteness`). -/
structure MinimalPremises where
  red_412_34 : ¬ CounterexampleAt ⟨(4, 12), 3, 4, 64⟩
  red_412_57 : ¬ CounterexampleAt ⟨(4, 12), 5, 7, 112⟩
  red_520_23 : ¬ CounterexampleAt ⟨(5, 20), 2, 3, 75⟩
  red_520_32 : ¬ CounterexampleAt ⟨(5, 20), 3, 2, 75⟩
  red_824_23 : ¬ CounterexampleAt ⟨(8, 24), 2, 3, 96⟩
  link_84 : CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ →
    ∃ (IM Im : Int), IM ≥ Im ∧ IM = 4 ∧ Im = 5
  prop329 : ∀ (a b : Nat), LPC (a, b) → b + Nat.gcd a b ≠ a
  link_120 : CounterexampleAt ⟨(8, 32), 3, 2, 120⟩ → LPC (8, 4)
  link_924 : CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ →
    ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76
  link_927 : CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ →
    ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76
  enum_complete : ∀ (degP degQ : Nat), Counterexample degP degQ →
    max degP degQ < 125 →
    ∃ r ∈ table, CounterexampleAt r ∧ degreePair r = (degP, degQ)

/-- `MinimalPremises.enum_complete` is exactly `TableCompleteness`. -/
theorem enum_complete_is_table_completeness
    (h : MinimalPremises CounterexampleAt Counterexample LPC) :
    TableCompleteness CounterexampleAt Counterexample :=
  h.enum_complete

/-- The red-row fields of `MinimalPremises` are exactly `RedRowPremises`. -/
theorem minimal_red_rows_are_red_row_premises
    (h : MinimalPremises CounterexampleAt Counterexample LPC) :
    RedRowPremises CounterexampleAt :=
  ⟨h.red_412_34, h.red_412_57, h.red_520_23, h.red_520_32, h.red_824_23⟩

/-- Theorem 2.1, from the minimal premises: if (P,Q) is a counterexample with
    max degree < 125, then (deg P, deg Q) ∈ {(72,108), (108,72)}.
    The (72,108) disjunct is the same (8,28) row with P and Q exchanged
    (`swapPair (108,72) = (72,108)`); the exchange is the Keller-condition
    symmetry `[Q,P] = -[P,Q]`, not a separate row. -/
theorem theorem21_minimal (h : MinimalPremises CounterexampleAt Counterexample LPC)
    (degP degQ : Nat) (hce : Counterexample degP degQ) (hmax : max degP degQ < 125) :
    (degP, degQ) = (72, 108) ∨ (degP, degQ) = (108, 72) := by
  obtain ⟨r, hr, hcr, hpair⟩ := h.enum_complete degP degQ hce hmax
  rcases table_cases r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hcr h.red_412_34
  · exact absurd hcr h.red_412_57
  · exact absurd hcr h.red_520_23
  · exact absurd hcr h.red_520_32
  · exact absurd hcr (discard_84_row CounterexampleAt h.link_84)
  · exact absurd hcr h.red_824_23
  · right
    exact hpair.symm
  · exact absurd hcr (discard_120_row CounterexampleAt LPC h.prop329 h.link_120)
  · exact absurd hcr (discard_924_row CounterexampleAt h.link_924)
  · exact absurd hcr (discard_927_row CounterexampleAt h.link_927)

/-- Theorem 2.1 in conditional form (same statement, premises packaged). -/
theorem theorem21_conditional_minimal (h : MinimalPremises CounterexampleAt Counterexample LPC)
    (degP degQ : Nat) (hce : Counterexample degP degQ) (hmax : max degP degQ < 125) :
    (degP, degQ) = (72, 108) ∨ (degP, degQ) = (108, 72) :=
  theorem21_minimal CounterexampleAt Counterexample LPC h degP degQ hce hmax

/-! ### Discharge audit (for the leg report — NOT a theorem)

| MinimalPremises field | Status after Leg A | Unblocks on |
|---|---|---|
| 1–5 red rows | CARRIED (cited theorems) | Leg F R20: [GGV4] §3.5, [M], [H], [GGV3] §5, [GGV5] Prop 6.1 |
| 6 link_84 | CARRIED | Leg F: [GGV6] Thm 7.3 + π-root machinery |
| 7 prop329 | CARRIED | Leg F: [GGV2] Prop 3.29 |
| 8 link_120 | CARRIED | Leg F: last-possible-corner computation (+ Thm 7.6(5) numbering; published §7 NOT FOUND) |
| 9 link_924 | CARRIED | Legs B/C: Prop 4.2 + §5 elimination (+ hybrid-vs-slip, published §7 NOT FOUND) |
| 10 link_927 | CARRIED | Legs B/C: Prop 4.1 + §5 elimination + Cor 5.7 step |
| 11 enum_complete | CARRIED | Leg F R19: [GGV5] §§5–6 enumeration completeness |

No `theorem21_unconditional` is claimed. The §3 arithmetic (E3/E4) and the
§2 table arithmetic (E2) are KERNEL in this file; everything else in E1–E4
is CONDITIONAL on the named premises above.
-/

/-!
# GGHV §4 — Propositions 4.1–4.4 + Algorithm PossibleStartingPoints (Leg B, Phase 4)

**CLAIM:** The four §4 Newton-polygon reduction propositions (E5–E8) are proved
as conditional Lean theorems from explicitly named premise structures, and
Algorithm PossibleStartingPoints (E9) is implemented in Lean with its output
on `(l,a,b) = (1,8,3)` proved by kernel `decide`. Every decidable arithmetic
step in the paper's §4 proofs (sieve tables, k-determinations, φ-maps on
vertex lists, Jacobian-factor pairs, Cor 7.4 numeric data, the (7,21)
ℓ-normalisation) is proved KERNEL (no premises). The cited external steps
are carried as named fields, never smuggled into a kernel claim.
**STATUS:** PROVED (conditional, per-item — see the verdict table at the end
of this file) — VERIFIED on lean-build-3, Lean 4.34.0, 2026-11-06: FULL run
exit 0 (7 s), axioms as listed in the verdict table (all permitted-triple
subsets, no `sorryAx`); second-tool Python recomputation ALL PASS (see
`check_s4_second_tool.py`, run on lean-build-3, Python 3.11.2, exit 0).

## Sources (all read before writing)

- Paper text: `~/workspace/research/rss-monitor/tex/2204.14178/main.tex`,
  §4 lines 457–1398 (Prop 4.1 TeX 463–469, proof 470–666; Prop 4.2 TeX 668–680,
  proof 681–997; Prop 4.3 TeX 1000–1007, proof 1008–1311; Prop 4.4 TeX 1313–1319,
  proof 1387–1396; Algorithm TeX 698–727).
- Statement inventory: `~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/gghv_statement_inventory.md`,
  entries E5–E9 (authoritative for what is open per item).
- Phase 1 baseline (cited, not re-derived): `d1_cor74_2026-11-05.lean`
  (`Cor74Data`, `cor74_prop42`, `cor74_prop43`, `cor74_721`, `ell721_normalization`,
  `cor74_F_conditional`/`cor74_F1_conditional`),
  `d1_esquina1_2026-11-05.lean` (`esquina_item1`),
  `d1_esquina2_2026-11-05.lean` (`esquina_item2`, `esquina_item2_k1`),
  `d1_assembly_2026-11-05.lean` (premise-structure pattern: `MinimalPremises`,
  link hypotheses over abstract predicates),
  `composition_2026-11-04.lean` (`branch_c_eliminated`) and
  `bridge_attempt_2026_11_04.lean` (`challenge_target`).
- Retrieval leg (closed 2026-11-06, `hidden_files/phase4/retrieval/retrieval_log.md`):
  published [GGV1] §7 text NOT FOUND (routes T1-R1–R15 exhausted); Joseph Lemma 2.2
  NOT FOUND (routes T2-R1–R12 exhausted). So hybrid-vs-slip stays carried.

## Formalisation level (read this before judging a verdict)

The paper's §4 arguments are about Laurent polynomials `P, Q ∈ L^{(1)}`, their
Newton polygons, directions, and automorphisms `φ`. There is NO Laurent-polynomial
/ Newton-polygon library in this workspace (the D2 polynomial layer, R14, is Leg E
work; the Laurent-series library is INTERFACE). Following Phase 1's established
style (`d1_assembly`, `d1_cor74`), this file formalises §4 at **vertex-list level**:
a Newton polygon is a `List (Int × Int)` of its vertices; `φ₁` (swap) and the
final morphisms `φ(x) = x⁻¹, φ(y) = x^c·y` are explicit point maps (`swapPt`,
`phiPow`); a shear `φ₂/φ₃` cutting one corner is the explicit `cutPt` map.
The **identification** of a model map with the paper's automorphism — i.e. that
`φ₂` really cuts exactly the stated corner, which is where Cor 7.4's edge form
enters — is NOT proved here; it is carried as a named premise field (an equality
about an opaque intermediate list). What IS proved kernel is: (a) the model maps
compute the paper's stated lists from the initial corners (`swap_927`,
`cut_927`, …); (b) all the paper's decidable arithmetic (sieve, k, φ-images,
Jacobian factors, Cor 7.4 data, algorithm output); (c) the assembly of the
final vertex lists + Jacobian-factor pair from the premise fields via (a)–(b).
So each `prop4X_conditional` is a genuine conditional theorem: its hypotheses
are exactly the paper's cited steps, and its proof does the paper's arithmetic.
Nothing here claims the polynomial-level propositions unconditionally.

## Per-item verdicts (to be confirmed by the VM run; see the table at the end)

- E5 Prop 4.1 (9,27): CONDITIONAL (`prop41_conditional` on `Prop41Premises`:
  Cor 7.4 edge step, φ₃ edge step, Prop 8.2 applied instance). Kernel: sieve
  table, k = 1, direction (−3,8), st values, φ-map, bracket factor (−1,1).
- E6 Prop 4.2 (9,24): CONDITIONAL (`prop42_conditional` on `Prop42Premises`:
  [GGV2] Prop 3.12 soundness link, [vdE] Prop 10.2.6 elimination link,
  hybrid-vs-slip, Prop 8.2-free). Kernel: Cor 7.4 (24,9) data, algorithm output
  + directions, R³ multiplicity count, three sub-case φ-maps, factor (−1,1).
- E7 Prop 4.3 (8,28): CONDITIONAL (`prop43_conditional` on `Prop43Premises`:
  [GGV2] Prop 3.12 setting, [GGV6] Prop 2.5 applied instance, hybrid-vs-slip,
  k = 2 exclusion). Kernel: Cor 7.4 (28,8) data, k ∈ {1,2}, (−2,7) face checks,
  (1,−3)-face check, three sub-case φ-maps, factor (−1,2). The case-split
  ELIMINATION is NOT redone: cases (a)/(b) by branches-(a),(b) `main_theorem`,
  case (c) by `branch_c_eliminated` — both kernel, permitted triple (Phase 1 /
  Step 1, commit 7e4db07f); cited narrowly in the header of §E7 below.
- E8 Prop 4.4 (7,21): CONDITIONAL (`prop44_conditional` on `Prop44Premises`:
  Cor 7.4 (q = 7) φ₂-cut link only). Kernel: the (7,21) Cor74Data bundle
  (re-pinned here self-contained; NOTE — the inventory's "still to add (i)"
  is STALE: `d1_cor74` already defines `cor74_721` + `ell721_normalization`),
  the ℓ-normalisation (support level, copied with attribution from `d1_cor74`),
  swap/cut/φ₃ maps, scalings ×2/×3, factor (−1,1). The paper's ℓ-formula is
  NOT copied literally: the correct face is `λ_p·x¹⁴·R¹⁴` (see `ell721_normalization`).
- E9 Algorithm: KERNEL implementation + output (`psp_183`, `psp_183_dirs`);
  its CORRECTNESS (that Pred_P(1,0) is among the output directions) is
  [GGV2] Prop 3.12 — carried as the `pred_sound` field of `Prop42Premises`
  (Leg F), NOT claimed here.

## Paper slips / corrections carried (not copied)

- E5: the paper states `m, n ∈ ℕ` but the esquina(2) step needs `m, n > 1`
  (Phase 1 finding, `CORRESPONDENCE.md`); `hmn` (m ≠ n) is unused.
- E6: the paper writes "`P ∈ kK[x,y]`" (TeX ~line 730, as printed); read as `K[x,y]`.
- E6/E7: [GGV2] Prop 3.12 numbers are `s = ϑ = 6`, `N₁ = 6`, `N₂ = 3` (integers),
  NOT 5/3, 3/2 (Phase 1 correction, `CORRESPONDENCE.md`).
- E7: Part 19's (8,28) exponents `4·2 = 8` are WRONG — `(m,n) = (3,2)`, so `4·3 = 12`.
- E8: the (7,21) ℓ-formula strips an `x¹⁴` factor (see above).
-/


/-! ## §0. Point arithmetic: the vertex-list model. -/

/-- A Newton-polygon vertex: an exponent pair `(a, b)` for `x^a y^b`. -/
abbrev Pt := Int × Int

/-- Cross product (2D determinant): `crossProd a b = a₁b₂ − a₂b₁`. -/
def crossProd (a b : Pt) : Int := a.1 * b.2 - a.2 * b.1

/-- Weighted valuation `dirVal ρ σ a b = ρa + σb` (Phase 1, verbatim). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Coordinate swap on a vertex: the effect of `φ₁(x) = y, φ₁(y) = x`. -/
def swapPt (p : Pt) : Pt := (p.2, p.1)

/-- The final morphism `φ(x) = x⁻¹, φ(y) = x^c·y` on a vertex:
    `x^a y^b ↦ x^{cb−a} y^b`. It is an involution. -/
def phiPow (c : Int) (p : Pt) : Pt := (c * p.2 - p.1, p.2)

/-- A shear cutting one corner: replace vertex `old` by `new`, leave the rest.
    This MODELS the paper's `φ₂`/`φ₃` steps (`y ↦ y + α x^{-k}`); the claim
    that the paper's shear acts as this cut is carried as a premise (see §E5–E8),
    while the computation `cutPt`-applied-to-explicit-lists is kernel. -/
def cutPt (old new : Pt) (p : Pt) : Pt := if p = old then new else p

/-- Scaling a vertex list by `k` (the `(m,n)`-multiplication of the paper's
    "corners multiplied by `(m,n)` respectively"). -/
def scalePt (k : Int) (p : Pt) : Pt := (k * p.1, k * p.2)

/-- Monomial Jacobian determinant of the exponent pairs `e₁, e₂`:
    `[x^{e₁}, x^{e₂}]` has coefficient `det(e₁,e₂)`. -/
def monJac (e₁ e₂ : Pt) : Int := e₁.1 * e₂.2 - e₁.2 * e₂.1

/-- The Jacobian-factor pair of the final morphism `φ(x) = x⁻¹, φ(y) = x^c·y`:
    `(det, x-exponent)`, so `[φ(x), φ(y)] = det · x^{c−2}` as a monomial.
    E5/E6/E8: `c = 3` gives `(−1, 1)`, i.e. `[φ(x),φ(y)] = −x`;
    E7: `c = 4` gives `(−1, 2)`, i.e. `[φ(x),φ(y)] = −x²`. The chain rule
    identifying `[φ(P),φ(Q)]` with `φ([P,Q])·[φ(x),φ(y)]` is R14 (Leg E);
    this pair is its numeric content, computed kernel here. -/
def phiJacPair (c : Int) : Pt := (monJac (-1, 0) (c, 1), c - 2)

theorem phiPow_involutive (c : Int) (p : Pt) : phiPow c (phiPow c p) = p := by
  obtain ⟨a, b⟩ := p
  rw [Prod.ext_iff]
  constructor
  · show c * b - (c * b - a) = a
    ring
  · rfl

theorem swapPt_involutive (p : Pt) : swapPt (swapPt p) = p := by
  obtain ⟨a, b⟩ := p
  rfl

theorem phiJacPair_3 : phiJacPair 3 = (-1, 1) := by decide

theorem phiJacPair_4 : phiJacPair 4 = (-1, 2) := by decide

/-- Cor 7.4 scaling relation (Phase 1 `d1_cor74`, verbatim): `enF = (p/q)·ab`. -/
def scaling (p q : Int) (enF ab : Pt) : Prop :=
  q * enF.1 = p * ab.1 ∧ q * enF.2 = p * ab.2

/-- Cor 7.4 instance data (Phase 1 `d1_cor74` `Cor74Data`, verbatim shape). -/
structure Cor74Data where
  dir : Pt
  ab : Pt
  p : Int
  q : Int
  hcop : Nat.gcd p.natAbs q.natAbs = 1
  enF : Pt
  hscale : scaling p q enF ab


/-! ## §E5. Proposition 4.1, case (9,27) — kernel arithmetic. -/

/-- The (9,27) base corners (TeX 470): `{(0,0),(1,0),(9,24),(9,27),(0,9)}`,
    multiplied by `(m,n) = (2,3)` respectively for `P` and `Q`. -/
def base927 : List Pt := [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)]

theorem scale2_base927 :
    base927.map (scalePt 2) = [(0, 0), (2, 0), (18, 48), (18, 54), (0, 18)] := by
  decide

theorem scale3_base927 :
    base927.map (scalePt 3) = [(0, 0), (3, 0), (27, 72), (27, 81), (0, 27)] := by
  decide

/-- `φ₁` (swap) on the base corners (kernel check of TeX 470–471). -/
theorem swap_927 :
    base927.map swapPt = [(0, 0), (0, 1), (24, 9), (27, 9), (9, 0)] := by
  decide

/-- `φ₂` cuts the `(9,0)` corner to `(−2,0)` (TeX 471: the edge
    `{(9,27),(0,9)}` is `y^9 (x y^2 − α₁)^9` by Cor 7.4, so `φ₂(y) = y + α₁x⁻²`
    cuts it). Kernel computation on the model; the identification
    model = `φ₂` is the `afterPhi2_eq` premise field below. -/
theorem cut_927 :
    (base927.map swapPt).map (cutPt (9, 0) (-2, 0)) =
      [(0, 0), (0, 1), (24, 9), (27, 9), (-2, 0)] := by
  decide

/-- `φ₃` cuts the `(0,1)` corner to `(21,8)` (TeX ~line 560: the edge
    `{(24,9),(0,1)}` is `y (y x^3 − α₂)^8`, so `φ₃(y) = y + α₂x⁻³` reduces it
    to `{(24,9),(21,8)}`). Kernel computation on the model, in the paper's
    listing order `{(0,0),(27,9),(24,9),(0,1),(−2,0)}` (a set, not a list). -/
theorem cut3_927 :
    ([(0, 0), (27, 9), (24, 9), (0, 1), (-2, 0)] : List Pt).map (cutPt (0, 1) (21, 8)) =
      [(0, 0), (27, 9), (24, 9), (21, 8), (-2, 0)] := by
  decide

/-- `cut_927`'s output and the paper's listing are the same SET (the paper
    lists corners as sets; the model map preserves the swap order). -/
theorem cut_927_set (e : Pt) :
    e ∈ [(0, 0), (0, 1), (24, 9), (27, 9), (-2, 0)] ↔
    e ∈ [(0, 0), (27, 9), (24, 9), (0, 1), (-2, 0)] := by
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

/-- The (9,27) Cor 7.4 F-instance (Phase 1 `d1_cor74` `cor74_927`, re-pinned):
    direction `(2,−1)`, `(a/l,b) = (9,27)`, `en(F) = (1,3) = (1/9)(9,27)`, `q = 9`. -/
def cor74_927_s4 : Cor74Data where
  dir := (2, -1)
  ab := (9, 27)
  p := 1
  q := 9
  hcop := by decide
  enF := (1, 3)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_927_s4_cond3 : cor74_927_s4.ab.2 > cor74_927_s4.ab.1 := by decide

theorem cor74_927_s4_exp_P : 9 * 2 = 18 := by decide

theorem cor74_927_s4_exp_Q : 9 * 3 = 27 := by decide

/-! ### E5 sieve (TeX ~lines 570–600).

The paper: with `(ρ₂,σ₂) = min{Succ_P(−1,3), Succ_Q(−1,3)}`, if
`en_{ρ₂,σ₂}(P) ∼ en_{ρ₂,σ₂}(Q)` then
`(a',b') = (1/2) en(P) = (1/3) en(Q)` is one of
`{(−2,0),(−1,0),(1,1),(2,1),(4,2),(5,2),(7,3),(10,4),(13,5)}`.
The corner of `F` other than `(1,1)` is
`(1,1) + c(21−a',8−b')/gcd(21−a',8−b')` for some `c > 0`, and computing
`v_{−8,21}` gives `13·gcd(21−a',8−b') + c(8a' − 21b') = 0`, hence
`21b' − 8a' ∣ 13·gcd(21−a',8−b')`. Only `(5,2)` and `(13,5)` survive
(`(1,1)` is excluded separately: `(a',b')` cannot lie on the diagonal). -/

/-- The sieve divisibility condition, Bool-valued for `List.filter`. -/
def sieveOkB (a' b' : Int) : Bool :=
  decide ((21 * b' - 8 * a') ∣ 13 * (Int.gcd (21 - a') (8 - b') : Int))

theorem sieveOkB_iff (a' b' : Int) :
    sieveOkB a' b' = true ↔ (21 * b' - 8 * a') ∣ 13 * (Int.gcd (21 - a') (8 - b') : Int) := by
  simp only [sieveOkB, decide_eq_true_eq]

/-- The nine candidate points from the paper. -/
def sieveCandidates927 : List Pt :=
  [(-2, 0), (-1, 0), (1, 1), (2, 1), (4, 2), (5, 2), (7, 3), (10, 4), (13, 5)]

/-- The paper's sieve table, recomputed (TeX ~line 595):
    `(−2,0) → 16 ∤ 13`; `(−1,0) → 8 ∤ 26`; `(2,1) → 5 ∤ 13`;
    `(4,2) → 10 ∤ 13`; `(5,2) → 2 ∣ 26`; `(7,3) → 7 ∤ 13`;
    `(10,4) → 4 ∤ 13`; `(13,5) → 1 ∣ 13`. Only `(5,2)`, `(13,5)` survive.
    Note `(1,1)` is IN the filtered list below only if it passed — it does
    pass the divisibility (`13 ∣ 13`), so the table below EXCLUDES it by
    hand, exactly as the paper does (diagonal argument, not the sieve);
    see `sieve_diag_passes`. -/
theorem sieve_table_927 :
    (sieveCandidates927.filter fun p => sieveOkB p.1 p.2) =
      [(1, 1), (5, 2), (13, 5)] := by
  decide

/-- `(1,1)` passes the divisibility condition — the paper excludes it by the
    diagonal argument ("`(a',b')` cannot lie on the diagonal"), not by the sieve.
    Recorded so the sieve verdict is not overstated. -/
theorem sieve_diag_passes : sieveOkB 1 1 = true := by decide

theorem sieve_diag_value : (21 * (1 : Int) - 8 * 1) = 13 ∧
    13 * (Int.gcd (21 - 1) (8 - 1) : Int) = 13 := by decide

/-- The `v_{−8,21}` derivation (TeX ~line 585): from
    `13·g + c·(8a' − 21b') = 0` the divisibility `21b' − 8a' ∣ 13·g` follows.
    Pure integer arithmetic, kernel. -/
theorem sieve_derivation (a' b' c g : Int)
    (h : 13 * g + c * (8 * a' - 21 * b') = 0) :
    (21 * b' - 8 * a') ∣ 13 * g := by
  refine ⟨c, ?_⟩
  linear_combination h

/-- The eight non-diagonal rows of the paper's table, one by one (kernel). -/
theorem sieve_rows_927 :
    (¬ (16 : Int) ∣ 13) ∧ (¬ (8 : Int) ∣ 26) ∧ (¬ (5 : Int) ∣ 13) ∧
    (¬ (10 : Int) ∣ 13) ∧ ((2 : Int) ∣ 26) ∧ (¬ (7 : Int) ∣ 13) ∧
    (¬ (4 : Int) ∣ 13) ∧ ((1 : Int) ∣ 13) := by
  decide

/-! ### E5 esquina / k = 1 / direction (−3,8) (TeX ~lines 600–640).

Prop 8.2 gives `k ∈ ℕ` with `(k+1)b < a` and
`{en(P), en(Q)} = {(−k,0), (k+1,1)}` for `(a,b)` one of
`{(21,8), (13,5), (5,2)}`. In all cases `k = 1`, so the ends are
`{(−1,0), (2,1)}` with direction `(ρ,σ) = (−3,8)`. -/

/-- `k = 1` from the three inequalities + `k ≥ 1` (the `(5,2)` row forces it:
    `(k+1)·2 < 5` gives `k ≤ 1`). Kernel, by `omega`. -/
theorem esquina_k1_927 (k : ℕ) (hk1 : 1 ≤ k)
    (h21 : (k + 1) * 8 < 21) (_h13 : (k + 1) * 5 < 13) (_h5 : (k + 1) * 2 < 5) :
    k = 1 := by
  omega

/-- The `k ∈ {1,2}`-style bound for the `(21,8)` row alone (used in E7's form). -/
theorem esquina_k12_218 (k : ℕ) (hk1 : 1 ≤ k) (h21 : (k + 1) * 8 < 21) :
    k = 1 ∨ k = 2 := by
  omega

/-- `st_{−3,8}(P) = (42,16) = 2·(21,8)` and `st_{−3,8}(Q) = (63,24) = 3·(21,8)`. -/
theorem st_927 : (2 * (21 : Int), 2 * 8) = (42, 16) ∧ (3 * 21, 3 * 8) = (63, 24) := by
  decide

/-- `dirVal (−3,8)` is constant on the two esquina edges:
    `(42,16)–(2,1)` for `P` (value 2) and `(63,24)–(−1,0)` for `Q` (value 3),
    so `(−3,8)` is the face direction of both. -/
theorem dir_38_927 :
    dirVal (-3) 8 42 16 = dirVal (-3) 8 2 1 ∧
    dirVal (-3) 8 63 24 = dirVal (-3) 8 (-1) 0 := by
  decide

/-- `(-3,8) × ((42,16) − (−1,0)) ≠ 0` (TeX ~line 640, "in fact … ≠ 0"). -/
theorem cross_38_927 : crossProd (-3, 8) ((42, 16) - (-1, 0)) ≠ 0 := by
  decide

/-- The final morphism `φ(x) = x⁻¹, φ(y) = x³y` on the pre-φ polygons
    (TeX ~lines 650–666). Pre-φ `P` vertices `(0,0),(2,1),(42,16),(48,18),(54,18)`
    (i.e. `(0,0)`, `en = (2,1)`, `st = (42,16)`, `2·(24,9)`, `2·(27,9)`);
    pre-φ `Q` vertices `(0,0),(−1,0),(63,24),(72,27),(81,27)`. -/
theorem phi3_927P :
    ([(0, 0), (2, 1), (42, 16), (48, 18), (54, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)] := by
  decide

theorem phi3_927Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27), (81, 27)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)] := by
  decide

/-! ### E5 conditional theorem.

Premise fields (each = one cited step of the paper's proof, stated about the
opaque intermediate lists):
- `afterPhi2_eq`: Cor 7.4 edge form + `φ₁, φ₂` — the post-`φ₁∘φ₂` base polygon
  is `{(0,0),(27,9),(24,9),(0,1),(−2,0)}`.
- `afterPhi3_eq`: the `{(24,9),(0,1)}` edge form + `φ₃` — the post-`φ₃` base
  polygon is `{(0,0),(27,9),(24,9),(21,8),(−2,0)}`.
- `k` + inequalities + ends + `st`/`dir`: [GGV1] Prop 8.2 applied (kernel in
  Phase 1: `d1_esquina1`/`d1_esquina2`; restated here as the applied instance),
  plus the paper's `st`/`dir` computation.
The `phi3_of_phi2_927` and `pre927_top` link lemmas relate the opaque fields
through the kernel model maps; the main theorem assembles them. -/

structure Prop41Premises where
  afterPhi2 : List Pt
  afterPhi2_eq : afterPhi2 = [(0, 0), (27, 9), (24, 9), (0, 1), (-2, 0)]
  afterPhi3 : List Pt
  afterPhi3_eq : afterPhi3 = [(0, 0), (27, 9), (24, 9), (21, 8), (-2, 0)]
  k : ℕ
  k_ge1 : 1 ≤ k
  k_ineq21 : (k + 1) * 8 < 21
  k_ineq13 : (k + 1) * 5 < 13
  k_ineq5 : (k + 1) * 2 < 5
  enP : Pt
  enP_eq : enP = ((k + 1 : ℤ), 1)
  enQ : Pt
  enQ_eq : enQ = (-(k : ℤ), 0)
  stP : Pt
  stP_eq : stP = (42, 16)
  stQ : Pt
  stQ_eq : stQ = (63, 24)
  dirE : Pt
  dirE_eq : dirE = (-3, 8)

/-- The `φ₃` step as a relation between the two opaque lists (kernel cut). -/
theorem phi3_of_phi2_927 (h : Prop41Premises) :
    h.afterPhi3 = h.afterPhi2.map (cutPt (0, 1) (21, 8)) := by
  rw [h.afterPhi3_eq, h.afterPhi2_eq]
  decide

/-- The top edge of the post-`φ₃` polygon, scaled for `P`/`Q`, contains the
    pre-`φ` vertices `(48,18) = 2·(24,9)`, `(54,18) = 2·(27,9)` (resp.
    `(72,27) = 3·(24,9)`, `(81,27) = 3·(27,9)`). -/
theorem pre927_top (h : Prop41Premises) :
    (48, 18) ∈ h.afterPhi3.map (scalePt 2) ∧ (54, 18) ∈ h.afterPhi3.map (scalePt 2) ∧
    (72, 27) ∈ h.afterPhi3.map (scalePt 3) ∧ (81, 27) ∈ h.afterPhi3.map (scalePt 3) := by
  rw [h.afterPhi3_eq]
  decide

/-- The pre-`φ` polygons assembled from the premise fields. -/
def preP927 (h : Prop41Premises) : List Pt := [(0, 0), h.enP, h.stP, (48, 18), (54, 18)]

def preQ927 (h : Prop41Premises) : List Pt := [(0, 0), h.enQ, h.stQ, (72, 27), (81, 27)]

/-- Proposition 4.1 (E5), CONDITIONAL: from the premise structure, the final
    vertex lists are exactly the paper's, and the Jacobian-factor pair is
    `(−1, 1)` (so `[φ(P),φ(Q)] = −[P,Q]·x`, and with `[P,Q] = −1` after the
    swap this is `x` up to the paper's rescaling). The polynomial-level
    statement ("there exist `P, Q ∈ L^{(1)}` with `[P,Q] = x`") is NOT claimed:
    it needs the Laurent layer (R14/INTERFACE). -/
theorem prop41_conditional (h : Prop41Premises) :
    ∃ finalP finalQ : List Pt,
      finalP = (preP927 h).map (phiPow 3) ∧
      finalQ = (preQ927 h).map (phiPow 3) ∧
      finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)] ∧
      finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)] ∧
      phiJacPair 3 = (-1, 1) := by
  have hk : h.k = 1 := esquina_k1_927 h.k h.k_ge1 h.k_ineq21 h.k_ineq13 h.k_ineq5
  have henP : h.enP = (2, 1) := by rw [h.enP_eq, hk]; decide
  have henQ : h.enQ = (-1, 0) := by rw [h.enQ_eq, hk]; decide
  have _hphi3 := phi3_of_phi2_927 h
  have _htop := pre927_top h
  refine ⟨(preP927 h).map (phiPow 3), (preQ927 h).map (phiPow 3), rfl, rfl, ?_, ?_, ?_⟩
  · show ([(0, 0), h.enP, h.stP, (48, 18), (54, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]
    rw [henP, h.stP_eq]
    exact phi3_927P
  · show ([(0, 0), h.enQ, h.stQ, (72, 27), (81, 27)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]
    rw [henQ, h.stQ_eq]
    exact phi3_927Q
  · exact phiJacPair_3


/-! ## §E9. Algorithm PossibleStartingPoints (TeX 698–727).

Input: a corner `(a/l, b) ∈ (1/l)ℕ × ℕ`. Output: the list of points `(c/l, d)`
such that equation (condicion) `[R,G] = R^i` (TeX 691) is satisfied.
Procedure (paper): for `d = 0` to `b−1`, for `c = ⌊d·a/b⌋+1` to `ld+a−bl−1`:
`N₁ = gcd(a−c, b−d)`; `N₂ = gcd(c, d)`; `(ρ,σ) = dir((a/l,b)−(c/l,d))`;
`s = (ρa+σlb)/gcd(ρa+σlb, l(ρ+σ))`; include `(c/l,d)` iff
(`s ∣ N₂` and `d > 0`) or `s ≤ N₁`.

Formalisation notes:
- `dir((a/l,b)−(c/l,d))` is the primitive direction *perpendicular* to the
  difference: `(ρ,σ)` with `ρ(a−c) + σ(b−d) = 0`, normalised to `ρ > 0`.
  For `Δ = (u,v)` with `u,v > 0` that is `(v/g, −u/g)` with `g = gcd(u,v)`
  (`dirPerp` below). Check against the paper's conclusion: the included
  points' directions must be `{(1,−2),(2,−5)}` — verified in `psp_183_dirs`.
- `s` is computed over `ℤ` with `Int.natAbs` (the paper's numerator is positive
  in every case that occurs here; the `natAbs` form is the literal
  `gcd`-quotient for positive numerators).
- The candidate count for `(c,d)` is `(ld+a−bl−1) − (⌊d·a/b⌋+1) + 1`
  (Nat subtraction; exact here since the upper bound exceeds the lower in all
  three `d`-rows for `(1,8,3)`).
- CORRECTNESS is NOT proved here: that the output directions contain
  `Pred_P(1,0)` is [GGV2] Prop 3.12 (Leg F, proof-OPEN). It is carried as the
  `pred_sound` field of `Prop42Premises` below. -/

/-- Primitive perpendicular direction of `Δ = (u,v)`, `u,v > 0`, normalised
    to first component positive: `(v/g, −u/g)`, `g = gcd(u,v)`. -/
def dirPerp (u v : ℕ) : Pt :=
  (((v / Nat.gcd u v : ℕ) : Int), -((u / Nat.gcd u v : ℕ) : Int))

/-- The paper's `s = (ρa+σlb)/gcd(ρa+σlb, l(ρ+σ))`, as a natural number
    (positive-numerator form). -/
def pspS (l a b : ℕ) (ρ σ : Int) : ℕ :=
  (ρ * (a : Int) + σ * ((l : Int) * (b : Int))).natAbs /
    Nat.gcd (ρ * (a : Int) + σ * ((l : Int) * (b : Int))).natAbs
      (((l : Int) * (ρ + σ)).natAbs)

/-- Inclusion test for one candidate `(c,d)` (Bool-valued for `List.filter`). -/
def pspInclude (l a b : ℕ) (p : ℕ × ℕ) : Bool :=
  let c := p.1
  let d := p.2
  let n1 := Nat.gcd (a - c) (b - d)
  let n2 := Nat.gcd c d
  let dir := dirPerp (a - c) (b - d)
  let s := pspS l a b dir.1 dir.2
  (decide (s ∣ n2) && decide (0 < d)) || decide (s ≤ n1)

/-- All candidates `(c,d)` for the paper's double loop. -/
def pspCandidates (l a b : ℕ) : List (ℕ × ℕ) :=
  (List.range b).flatMap fun d =>
    (List.range (l * d + a - b * l - d * a / b - 1)).map
      fun k => (d * a / b + 1 + k, d)

/-- Algorithm PossibleStartingPoints (E9), as a Lean function. -/
def possibleStartingPoints (l a b : ℕ) : List (ℕ × ℕ) :=
  (pspCandidates l a b).filter (pspInclude l a b)

/-- The paper's application (TeX 694): `(l,a,b) = (1,8,3)`. Candidates in
    loop order: `d=0: (1,0),(2,0),(3,0),(4,0)`; `d=1: (3,1),(4,1),(5,1)`;
    `d=2: (6,2)`. Included: `(2,0)` (`s=2 ≤ N₁=3`), `(3,1)` (`s=1 ≤ N₁=1`),
    `(4,1)` (`s=2 ≤ N₁=2`), `(6,2)` (`s=2 ∣ N₂=2`, `d>0`). Excluded:
    `(1,0)` (`s=3`, `N₁=1`, `3∤1`), `(3,0)` (`s=9`, `N₁=1`),
    `(4,0)` (`s=12`, `N₁=1`), `(5,1)` (`s=7`, `N₁=1`, `7∤1`). -/
theorem psp_183 : possibleStartingPoints 1 8 3 = [(2, 0), (3, 1), (4, 1), (6, 2)] := by
  decide

theorem psp_183_candidates : pspCandidates 1 8 3 =
    [(1, 0), (2, 0), (3, 0), (4, 0), (3, 1), (4, 1), (5, 1), (6, 2)] := by
  decide

/-- The directions of the output points are exactly `{(1,−2),(2,−5)}`
    (TeX 694: "shows that `Pred_P(1,0) ∈ {(1,−2),(2,−5)}`"). -/
theorem psp_183_dirs :
    (possibleStartingPoints 1 8 3).map (fun p => dirPerp (8 - p.1) (3 - p.2)) =
      [(1, -2), (2, -5), (1, -2), (1, -2)] := by
  decide

theorem psp_183_dirs_subset (d : Pt) :
    d ∈ (possibleStartingPoints 1 8 3).map (fun p => dirPerp (8 - p.1) (3 - p.2)) →
    d = (1, -2) ∨ d = (2, -5) := by
  rw [psp_183_dirs]
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

theorem psp_183_mem_31 : (3, 1) ∈ possibleStartingPoints 1 8 3 := by
  rw [psp_183]
  decide

/- The second application in the paper (TeX ~line 850): the algorithm with
    the same parameters shows `st_{ρ,σ}(φ₂(P)) ∈ 3m{(0,0),(3,1)}`; the `(3,1)`
    member is an algorithm output (kernel, above). The `(0,0)` member is the
    "edge completely cut" case, carried in the `aprime_mem` field below. -/


/-! ## §E6. Proposition 4.2, case (9,24) — kernel arithmetic. -/

/-- The (9,24) base corners (TeX 681): `{(0,0),(1,0),(9,24),(0,6)}`,
    multiplied by `(m,n) = (2,3)`. -/
def base924 : List Pt := [(0, 0), (1, 0), (9, 24), (0, 6)]

theorem swap_924 :
    base924.map swapPt = [(0, 0), (0, 1), (24, 9), (6, 0)] := by
  decide

/-- The Prop 4.2 Cor 7.4 instance (Phase 1 `d1_cor74` `cor74_prop42`, re-pinned):
    `(ρ₀,σ₀) = (−1,3)`, `(a/l,b) = (24,9)`, `en_{−1,3}(F) = (16,6) = (2/3)(24,9)`,
    so `q = 3`. MIXED slot (see header): F's condition (3) FAILS (`b < a/l`)
    while F1's HOLDS — the hybrid-vs-slip question, carried as a premise
    field (`hybrid_slip`) below, retrieval NOT FOUND. -/
def cor74_prop42_s4 : Cor74Data where
  dir := (-1, 3)
  ab := (24, 9)
  p := 2
  q := 3
  hcop := by decide
  enF := (16, 6)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_prop42_s4_cond3_fails : ¬ (cor74_prop42_s4.ab.2 > cor74_prop42_s4.ab.1) := by
  decide

theorem cor74_prop42_s4_cond3_F1 : cor74_prop42_s4.ab.2 < cor74_prop42_s4.ab.1 := by
  decide

theorem cor74_prop42_s4_exp : 3 * 2 = 6 := by decide

/-- `ℓ_{ρ,σ}(P) = λR^{3m}` with `en(R) = (8,3)`: `R^6` has endpoints
    `6·(2,0) = (12,0)` and `6·(8,3) = (48,18)` (Phase 1 `cor74_prop42_R`). -/
theorem cor74_prop42_s4_R :
    (6 * 2, 6 * 0) = (12, 0) ∧ (6 * 8, 6 * 3) = (48, 18) := by decide

theorem cor74_prop42_s4_cross : 0 < crossProd (1, -2) ((48, 18) - (12, 0)) := by
  decide

/-- [GGV2] Prop 3.12 numbers for the (9,24) application (TeX ~line 800):
    `s = ϑ = 6`, `N₁ = 6`, `N₂ = 3` (integers — NOT 5/3, 3/2). -/
theorem prop312_nums_924 : (6 : ℕ) = 6 ∧ (6 : ℕ) = 6 ∧ (3 : ℕ) = 3 := by decide

/-- The multiplicity count eliminating the three-factor case (TeX ~line 800):
    if `R` has three DISTINCT linear factors (multiplicities `[1,1,1]`), then
    `R^3` has multiplicities `[3,3,3]`, and no factor has multiplicity `6`.
    The existence of a factor of multiplicity `s = ϑ = 6` is [GGV2]
    Prop 3.12(2) — carried as the `r3mults`/`h312_2` fields below. -/
theorem r3_mults_924 : ([1, 1, 1] : List ℕ).map (· * 3) = [3, 3, 3] ∧
    (6 : ℕ) ∉ ([3, 3, 3] : List ℕ) := by
  decide

/-- The `φ₂` corners in the two-factor case (TeX ~line 810):
    `{(0,0),(18,6),(24,9),(0,1),(−2,0)}` (base, ×(2,3)). The `(18,6)` vertex
    is new (from the `R`-factor); the `(6,0)` corner is cut to `(−2,0)`. -/
theorem phi2cut_924 :
    ([(0, 0), (0, 1), (24, 9), (6, 0)] : List Pt).map (cutPt (6, 0) (-2, 0)) =
      [(0, 0), (0, 1), (24, 9), (-2, 0)] := by
  decide

/-- The edge `{(24,9),(0,1)}` transformed "exactly as in the case (9,27)"
    (TeX ~line 820): `φ₃` cuts `(0,1)` to `(21,8)`. Kernel computation. -/
theorem edge924_927 :
    ([(0, 0), (18, 6), (24, 9), (0, 1), (-2, 0)] : List Pt).map (cutPt (0, 1) (21, 8)) =
      [(0, 0), (18, 6), (24, 9), (21, 8), (-2, 0)] := by
  decide

/-- The three final shapes (TeX 668–680), and their pre-`φ` polygons under
    `φ(x) = x⁻¹, φ(y) = x³y` (same final morphism as E5). Pre-`φ` vertices:
    sub-case (1) `P`: `(0,0),(2,1),(42,16),(48,18),(36,12)` — note
    `(36,12) = 2·(18,6)` (the two-factor corner); `Q`: `(0,0),(−1,0),(63,24),
    (72,27),(54,18)` with `(54,18) = 3·(18,6)`.
    Sub-case (2): the `(a',b') = (9,3)` vertex: `(18,6) = 2·(9,3)` for `P`,
    `(27,9) = 3·(9,3)` for `Q`. Sub-case (3): `(a',b') = (0,0)`, no extra vertex. -/
theorem phi_924_sub1P :
    ([(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)] := by
  decide

theorem phi_924_sub1Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27), (54, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)] := by
  decide

theorem phi_924_sub2P :
    ([(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)] := by
  decide

theorem phi_924_sub2Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)] := by
  decide

theorem phi_924_sub3P :
    ([(0, 0), (2, 1), (42, 16), (48, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18)] := by
  decide

theorem phi_924_sub3Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27)] := by
  decide

/-- The `(a',b') ∈ {(0,0),(9,3)}` dichotomy, arithmetically: `(9,3)` scales to
    the sub-case (2) extra vertices `(18,6) = 2·(9,3)`, `(27,9) = 3·(9,3)`,
    and `(0,0)` to no extra vertex (sub-case (3)). -/
theorem aprime_924_scale :
    (2 * (9 : Int), 2 * 3) = (18, 6) ∧ (3 * 9, 3 * 3) = (27, 9) := by
  decide

/-! ### E6 conditional theorem.

Premise fields:
- `predP10` + `pred_sound`: [GGV2] Prop 3.12's soundness link — `Pred_P(1,0)`
  is among the algorithm's output directions (the algorithm itself is kernel,
  §E9; its correctness is Leg F). The kernel subset lemma then forces
  `predP10 ∈ {(1,−2),(2,−5)}`.
- `pred_ne_25`: [vdE] Prop 10.2.6 applied twice — `Pred_P(1,0) = (2,−5)` leads
  to `st_{2,−5}(P) = 3m(3,1)`, `Pred_P(2,−5) ≤ (1,−3)`, `deg_x(P(x,0)) ≤ 0`,
  contradicting [vdE] 10.2.6 (and likewise `st_{1,−2}(R) = (6,2)`).
  [vdE] Prop 10.2.6 itself has no Lean leg (Leg F / external).
- `stR12` + `stR12_mem`: `st_{1,−2}(R) ∈ {(2,0),(4,1)}` (paper's conclusion
  after the [vdE] eliminations).
- `rForm` + `rForm_mem`: `R` has 1, 2 or 3 distinct linear factors in `z = x²y`.
- `r3mults` + `h312_2` + `rform3`: [GGV2] Prop 3.12(2) applied — a linear
  factor of `R^3` has multiplicity `s = ϑ = 6`; with `R` three-factor
  (`rForm = 3`) the multiplicities are `[3,3,3]`, contradiction (kernel
  `r3_mults_924`). The `6` is the paper's number, not a model artefact.
- `postPhi2_924` + `postPhi2_924_eq`: the `φ₂` corners in the two-factor case
  (Cor 7.4 + `φ̄`); `edgeTrans924`: the `{(24,9),(0,1)}` edge transformed as
  in (9,27) (carried: the `φ₃` cut on this polygon).
- `aprime` + `aprime_mem`: in the one-factor case, the new preceding edge
  satisfies `(a',b') ∈ {(0,0),(9,3)}` (algorithm + `en F = (2/3)(9,24)`).
- `stR12_ne62`: `λ₁ ≠ 0`, second half (paper's argument: in the two-factor case
  `λ₁ = 0` implies `st_{ρ,σ}(R) = (6,2)`, impossible as above). Stated as a
  hypothesis about the opaque `stR12` (it is `(2,0)` or `(4,1)`, never `(6,2)`).
  The first half (`λ₁ = 0` implies `Pred_P(1,0) = (2,−5)` or `≤ (8,−3)` in the
  one-factor case) is already `pred_ne_25` + the algorithm directions.
- `hybrid_slip`: the hybrid-vs-slip reading for the swapped Cor 7.4 use
  (retrieval NOT FOUND 2026-11-06). The swapped Cor 7.4 conclusion as applied
  is: `R` exists with `en(R) = (8,3)` (kernel arithmetic, `cor74_prop42_s4_R`)
  AND the Cor 7.4 application to the mixed slot is valid. The validity is the
  carried content, so the structure takes it as an explicit `Prop` parameter
  (`HybridSlip924`), and the field `hybrid_slip` is a proof of it: the
  conditional theorem is then explicitly conditional on that named proposition.
  (A field of type `Prop` alone would be data, not a proof — hence the
  parameter + proof-field pattern, the same shape as `d1_assembly`'s abstract
  predicates `CounterexampleAt`/`LPC`.) -/

structure Prop42Premises (HybridSlip924 : Prop) where
  predP10 : Pt
  pred_sound : predP10 ∈
    (possibleStartingPoints 1 8 3).map (fun p => dirPerp (8 - p.1) (3 - p.2))
  pred_ne_25 : predP10 ≠ (2, -5)
  stR12 : Pt
  stR12_mem : stR12 = (2, 0) ∨ stR12 = (4, 1)
  stR12_ne62 : stR12 ≠ (6, 2)
  rForm : ℕ
  rForm_mem : rForm = 1 ∨ rForm = 2 ∨ rForm = 3
  r3mults : List ℕ
  h312_2 : (6 : ℕ) ∈ r3mults
  rform3 : rForm = 3 → r3mults = [3, 3, 3]
  postPhi2_924 : List Pt
  postPhi2_924_eq : postPhi2_924 = [(0, 0), (18, 6), (24, 9), (0, 1), (-2, 0)]
  edgeTrans924 : postPhi2_924.map (cutPt (0, 1) (21, 8)) =
    [(0, 0), (18, 6), (24, 9), (21, 8), (-2, 0)]
  aprime : Pt
  aprime_mem : aprime = (0, 0) ∨ aprime = (9, 3)
  hybrid_slip : HybridSlip924

/-- `Pred_P(1,0) = (1,−2)`: from Prop 3.12 soundness (field) + the kernel
    algorithm directions + the [vdE] elimination of `(2,−5)`. -/
theorem predP10_eq_924 {H : Prop} (h : Prop42Premises H) : h.predP10 = (1, -2) := by
  have hmem := psp_183_dirs_subset h.predP10 h.pred_sound
  rcases hmem with h1 | h2
  · exact h1
  · exact absurd h2 h.pred_ne_25

/-- The three-factor case is impossible (kernel count + Prop 3.12(2) field). -/
theorem rform_ne3_924 {H : Prop} (h : Prop42Premises H) : h.rForm ≠ 3 := by
  intro h3
  have hmul := h.rform3 h3
  have h312 := h.h312_2
  rw [hmul] at h312
  exact (r3_mults_924.2) h312

/-- The pre-`φ` polygons assembled from the premise fields.
    Two-factor case (`rForm = 2`): the `(36,12) = 2·(18,6)` / `(54,18) = 3·(18,6)`
    vertices come from `postPhi2_924` (see `pre924_2_top`); the `(42,16)` /
    `(48,18)` vertices from the edge transformation (see `pre924_2_edge`).
    One-factor case (`rForm = 1`): the extra vertex is `(18,6) = 2·(9,3)` /
    `(27,9) = 3·(9,3)` iff `(a',b') = (9,3)`, else absent. -/
def preP924_2 {H : Prop} (_h : Prop42Premises H) : List Pt :=
  [(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)]

def preQ924_2 {H : Prop} (_h : Prop42Premises H) : List Pt :=
  [(0, 0), (-1, 0), (63, 24), (72, 27), (54, 18)]

def preP924_1 {H : Prop} (h : Prop42Premises H) : List Pt :=
  if h.aprime = (9, 3) then [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
  else [(0, 0), (2, 1), (42, 16), (48, 18)]

def preQ924_1 {H : Prop} (h : Prop42Premises H) : List Pt :=
  if h.aprime = (9, 3) then [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
  else [(0, 0), (-1, 0), (63, 24), (72, 27)]

/-- The two-factor corner `(18,6)` of `postPhi2_924`, scaled for `P`/`Q`. -/
theorem pre924_2_top {H : Prop} (h : Prop42Premises H) :
    (36, 12) ∈ h.postPhi2_924.map (scalePt 2) ∧
    (54, 18) ∈ h.postPhi2_924.map (scalePt 3) := by
  rw [h.postPhi2_924_eq]
  decide

/-- The edge-transformed vertices `(42,16) = 2·(21,8)`, `(48,18) = 2·(24,9)`
    (and the `Q` analogues) in the edge-transformed, scaled polygon. -/
theorem pre924_2_edge {H : Prop} (h : Prop42Premises H) :
    (42, 16) ∈ (h.postPhi2_924.map (cutPt (0, 1) (21, 8))).map (scalePt 2) ∧
    (48, 18) ∈ (h.postPhi2_924.map (cutPt (0, 1) (21, 8))).map (scalePt 2) := by
  rw [h.edgeTrans924]
  decide

/-- Proposition 4.2 (E6), CONDITIONAL: from the premise structure, one of the
    three final shapes holds, with Jacobian-factor pair `(−1,1)`.
    Sub-case (1) ← `rForm = 2` (two-factor `R`); sub-case (2) ← `rForm = 1`
    with `(a',b') = (9,3)`; sub-case (3) ← `rForm = 1` with `(a',b') = (0,0)`.
    The polynomial-level statement is NOT claimed (Laurent layer, R14). -/
theorem prop42_conditional {H : Prop} (h : Prop42Premises H) :
    ∃ finalP finalQ : List Pt,
      ((finalP = (preP924_2 h).map (phiPow 3) ∧
        finalQ = (preQ924_2 h).map (phiPow 3) ∧
        finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)] ∧
        finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)]) ∨
       (finalP = (preP924_1 h).map (phiPow 3) ∧
        finalQ = (preQ924_1 h).map (phiPow 3) ∧
        ((finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)] ∧
          finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)]) ∨
         (finalP = [(0, 0), (1, 1), (6, 16), (6, 18)] ∧
          finalQ = [(0, 0), (1, 0), (9, 24), (9, 27)])))) ∧
      phiJacPair 3 = (-1, 1) := by
  have _hst := h.stR12_mem
  have _hne62 := h.stR12_ne62
  have _htop := pre924_2_top h
  have _hedge := pre924_2_edge h
  have _hpred : h.predP10 = (1, -2) := predP10_eq_924 h
  rcases h.rForm_mem with h1 | h2 | h3
  · -- `R = x²(z−λ₁)³`: edge completely cut; `(a',b') ∈ {(0,0),(9,3)}`.
    rcases h.aprime_mem with ha | ha
    · -- `(a',b') = (0,0)` → sub-case (3).
      have hne : h.aprime ≠ (9, 3) := by rw [ha]; decide
      have eP : preP924_1 h = [(0, 0), (2, 1), (42, 16), (48, 18)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
          else [(0, 0), (2, 1), (42, 16), (48, 18)]) = [(0, 0), (2, 1), (42, 16), (48, 18)]
        rw [if_neg hne]
      have eQ : preQ924_1 h = [(0, 0), (-1, 0), (63, 24), (72, 27)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
          else [(0, 0), (-1, 0), (63, 24), (72, 27)]) = [(0, 0), (-1, 0), (63, 24), (72, 27)]
        rw [if_neg hne]
      refine ⟨(preP924_1 h).map (phiPow 3), (preQ924_1 h).map (phiPow 3),
        Or.inr ⟨rfl, rfl, Or.inr ⟨?_, ?_⟩⟩, phiJacPair_3⟩
      · rw [eP]
        exact phi_924_sub3P
      · rw [eQ]
        exact phi_924_sub3Q
    · -- `(a',b') = (9,3)` → sub-case (2).
      have eP : preP924_1 h = [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
          else [(0, 0), (2, 1), (42, 16), (48, 18)]) =
          [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
        rw [if_pos ha]
      have eQ : preQ924_1 h = [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
          else [(0, 0), (-1, 0), (63, 24), (72, 27)]) =
          [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
        rw [if_pos ha]
      refine ⟨(preP924_1 h).map (phiPow 3), (preQ924_1 h).map (phiPow 3),
        Or.inr ⟨rfl, rfl, Or.inl ⟨?_, ?_⟩⟩, phiJacPair_3⟩
      · rw [eP]
        exact phi_924_sub2P
      · rw [eQ]
        exact phi_924_sub2Q
  · -- `R = x²(z−λ₁)²(z−λ₂)`: `φ₂` corners + edge as in (9,27) → sub-case (1).
    refine ⟨(preP924_2 h).map (phiPow 3), (preQ924_2 h).map (phiPow 3),
      Or.inl ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_3⟩
    · show ([(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)] : List Pt).map (phiPow 3) =
        [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)]
      exact phi_924_sub1P
    · show ([(0, 0), (-1, 0), (63, 24), (72, 27), (54, 18)] : List Pt).map (phiPow 3) =
        [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)]
      exact phi_924_sub1Q
  · exact absurd h3 (rform_ne3_924 h)


/-! ## §E7. Proposition 4.3, case (8,28) — kernel arithmetic.

NOTE ON SCOPE (read first): the proposition's FULL statement is the polygon
reduction (proved conditionally below). The ELIMINATION of the two resulting
shapes is already KERNEL and is NOT redone here:
- item (2) (cases (a),(b)) by the branches-(a),(b) `main_theorem` (kernel,
  permitted triple; `CORRESPONDENCE.md`, "Relation to the branch packages");
- item (1) (case (c)) by `branch_c_eliminated`
  (`composition_2026-11-04.lean`, line 13: no `∃ P Q lam`, `lam ≠ 0 ∧
  NewtonNFc P Q ∧ jac P Q = C lam * X 0 ^ 2`, any characteristic-0 field;
  kernel, no hypotheses, permitted triple) via `challenge_target`
  (`bridge_attempt_2026_11_04.lean`, line 43) — filed 2026-11-06 as tracked
  modules `GradeA.Bridge` / `GradeA.Composition` (commit `7e4db07f`, fork main,
  re-verified on lean-build-3).
What remains open for E7 (and is done here) is the reduction chain itself:
the `φ₁/φ₂/φ₃/φ` polygon chain, the derivation of sub-cases (a)/(b)/(c), the
`Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)` determination, the `k ∈ {1,2}` analysis
and the `k = 2` impossibility. -/

/-- The (8,28) base corners (TeX 1008): `{(0,0),(1,0),(8,28),(0,4)}`,
    multiplied by `(m,n) = (3,2)`. -/
def base828 : List Pt := [(0, 0), (1, 0), (8, 28), (0, 4)]

theorem swap_828 :
    base828.map swapPt = [(0, 0), (0, 1), (28, 8), (4, 0)] := by
  decide

/-- The Prop 4.3 Cor 7.4 instance (Phase 1 `d1_cor74` `cor74_prop43`, re-pinned):
    `(ρ₀,σ₀) = (−1,4)`, `(a/l,b) = (28,8)`, `en_{−1,4}(F) = (21,6) = (3/4)(28,8)`,
    so `q = 4`. MIXED slot (hybrid-vs-slip, carried — retrieval NOT FOUND). -/
def cor74_prop43_s4 : Cor74Data where
  dir := (-1, 4)
  ab := (28, 8)
  p := 3
  q := 4
  hcop := by decide
  enF := (21, 6)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_prop43_s4_cond3_fails : ¬ (cor74_prop43_s4.ab.2 > cor74_prop43_s4.ab.1) := by
  decide

theorem cor74_prop43_s4_cond3_F1 : cor74_prop43_s4.ab.2 < cor74_prop43_s4.ab.1 := by
  decide

/-- `qm = 4·3 = 12` — NOT `4·2 = 8` (Part 19's error: `(m,n) = (3,2)` here). -/
theorem cor74_prop43_s4_exp : 4 * 3 = 12 := by decide

/-- `ℓ_{ρ,σ}(P) = λR^{4m}` with `en(R) = (7,2)`: `R^12` has endpoints
    `12·(1,0) = (12,0)` and `12·(7,2) = (84,24)` (Phase 1 `cor74_prop43_R`). -/
theorem cor74_prop43_s4_R :
    (12 * 1, 12 * 0) = (12, 0) ∧ (12 * 7, 12 * 2) = (84, 24) := by
  decide

theorem cor74_prop43_s4_cross : 0 < crossProd (1, -3) ((84, 24) - (12, 0)) := by
  decide

/-- The `(1,−3)`-face check for case (c) (TeX ~line 1150):
    `ℓ_{1,−3}(P) = λ x^{4m}(x³y−α₁)^{4m}(x³y−α₂)^{4m}` — the vertices
    `m(16,4) = (48,12)`, `m(28,8) = (84,24)` and `(12,0)` all have
    `dirVal (1,−3) = 12`, i.e. they lie on the same `(1,−3)`-face. -/
theorem face13_828 :
    dirVal 1 (-3) 48 12 = dirVal 1 (-3) 84 24 ∧ dirVal 1 (-3) 12 0 = 12 := by
  decide

/-- The `Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)` determination, checked:
    `(−2,7)` is the face direction of the esquina edges — `dirVal (−2,7)`
    is `3` on `(2,1)` and on `3·(24,7) = (72,21)`, and `2` on `(−1,0)` and
    on `2·(24,7) = (48,14)`. -/
theorem dir_27_828 :
    dirVal (-2) 7 2 1 = dirVal (-2) 7 72 21 ∧
    dirVal (-2) 7 (-1) 0 = dirVal (-2) 7 48 14 := by
  decide

/-- `k ∈ {1,2}` from the loosest `(a,b) = (24,7)` row: `(k+1)·7 < 24`.
    Stated over `ℤ` (with `↑k`) to match E7's `k_ineq`, whose `(a,b)` are `Pt`
    components. -/
theorem esquina_k12_247 (k : ℕ) (hk1 : 1 ≤ k) (h247 : ((k : Int) + 1) * 7 < 24) :
    k = 1 ∨ k = 2 := by
  omega

/-- `k = 1` from the tightest `(a,b) = (3,1)` row: `(k+1)·1 < 3`.
    Stated over `ℤ` (with `↑k`) to match E7's `k_ineq`. -/
theorem esquina_k1_31 (k : ℕ) (hk1 : 1 ≤ k) (h31 : ((k : Int) + 1) * 1 < 3) :
    k = 1 := by
  omega

/-- The three lower-side shapes (TeX ~lines 1130–1140), base lists:
    (a) `{(-2,0),(0,0),(28,8),(0,1)}`; (b) `{(-3,0),(0,0),(28,8),(0,1)}`;
    (c) `{(-3,0),(0,0),(16,4),(28,8),(0,1)}` (all ×(m,n)). -/
theorem cut_lower_828_a :
    ([(-2, 0), (0, 0), (28, 8), (0, 1)] : List Pt).map (cutPt (0, 1) (24, 7)) =
      [(-2, 0), (0, 0), (28, 8), (24, 7)] := by
  decide

theorem cut_lower_828_b :
    ([(-3, 0), (0, 0), (28, 8), (0, 1)] : List Pt).map (cutPt (0, 1) (24, 7)) =
      [(-3, 0), (0, 0), (28, 8), (24, 7)] := by
  decide

theorem cut_lower_828_c :
    ([(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)] : List Pt).map
      (cutPt (0, 1) (24, 7)) =
      [(-3, 0), (0, 0), (16, 4), (28, 8), (24, 7)] := by
  decide

/-- The final morphism `φ(x) = x⁻¹, φ(y) = x⁴y` on the pre-`φ` polygons
    (TeX ~lines 1240–1311). Cases (a)/(b): `P` pre-vertices
    `(0,0),(−1,0),(48,14),(56,16)` — note `en(P) = (−1,0)` here (the paper
    sets `(en(Q),en(P)) = ((2,1),(−1,0))`, SWAPPED relative to E5, where
    `(m,n) = (2,3)` gave `en(P) = (2,1)`); `Q` pre-vertices
    `(0,0),(2,1),(72,21),(84,24)`. Case (c) adds `(32,8) = 2·(16,4)` for `P`
    and `(48,12) = 3·(16,4)` for `Q`. -/
theorem phi_828_abP :
    ([(0, 0), (-1, 0), (48, 14), (56, 16)] : List Pt).map (phiPow 4) =
      [(0, 0), (1, 0), (8, 14), (8, 16)] := by
  decide

theorem phi_828_abQ :
    ([(0, 0), (2, 1), (72, 21), (84, 24)] : List Pt).map (phiPow 4) =
      [(0, 0), (2, 1), (12, 21), (12, 24)] := by
  decide

theorem phi_828_cP :
    ([(0, 0), (-1, 0), (48, 14), (56, 16), (32, 8)] : List Pt).map (phiPow 4) =
      [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)] := by
  decide

theorem phi_828_cQ :
    ([(0, 0), (2, 1), (72, 21), (84, 24), (48, 12)] : List Pt).map (phiPow 4) =
      [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)] := by
  decide

/-! ### E7 conditional theorem.

Premise fields:
- `afterPhi1_eq`: `φ₁` swap (kernel `swap_828`) + Cor 7.4 set-up — the
  post-`φ₁` base polygon is `{(0,0),(0,1),(28,8),(4,0)}`.
- `pred_mem`: [GGV6] Prop 2.5 applied — `Pred_P(1,0) ∈ {(1,−2),(1,−3)}`
  (Prop 2.5 itself: instance layer only in Phase 1, `d1_ggvstar`
  `Prop25Instance`; proof OPEN, Leg F).
- `lower_eq`: the three lower-side shapes (a)/(b)/(c) — derived in the paper
  from `Pred_P(1,0)` via the `ℓ_{1,−2}`/`ℓ_{1,−3}` factor analysis.
- `k` + `k_ab_mem` + `k_ineq` + `k_ne2`: [GGV1] Prop 8.2 applied
  (`(a,b)` one of `{(24,7),(17,5),(10,3),(3,1)}`, `(k+1)b < a`), with the
  `k = 2` impossibility ("the edges of `P` and `Q` would have no way of being
  parallel") carried as `k_ne2`.
- `enP`/`enQ`/`stP`/`stQ`/`dirE`: the esquina ends (note the E7 swap:
  `en(P) = (−k,0)`, `en(Q) = (k+1,1)`) and the `st` values
  `st(P) = (48,14)`, `st(Q) = (72,21)` on the `(−2,7)`-face.
- `succP`/`succQ`: `Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)` (the "as in
  Prop 4.1" opposite-vertex analysis).
- `hybrid_slip`: hybrid-vs-slip for the swapped Cor 7.4 use (same pattern
  as E6: explicit `Prop` parameter + proof field).
[GGV2] Prop 3.12's role in E7 is the `R, G` setting (`[R,G] = R^i`,
`en(R) = (7,2)`); it is carried inside `pred_mem`'s justification (the Pred
restriction that Prop 2.5 refines) and named here: the structure's
`prop312_holds` field (explicit `Prop` parameter `Prop312_828`, same pattern
as `hybrid_slip`) records that the (8,28) `R/G` data satisfy Prop 3.12's
hypotheses. The `en(R) = (7,2)` + `v(R) > 0` content is kernel
(`cor74_prop43_s4_R`); the `[R,G]` equation itself needs the bracket layer
and is the carried part. -/

structure Prop43Premises (HybridSlip828 Prop312_828 : Prop) where
  afterPhi1 : List Pt
  afterPhi1_eq : afterPhi1 = [(0, 0), (0, 1), (28, 8), (4, 0)]
  predP10 : Pt
  pred_mem : predP10 = (1, -2) ∨ predP10 = (1, -3)
  lowerP : List Pt
  lower_eq : lowerP = [(-2, 0), (0, 0), (28, 8), (0, 1)] ∨
    lowerP = [(-3, 0), (0, 0), (28, 8), (0, 1)] ∨
    lowerP = [(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)]
  k : ℕ
  k_ge1 : 1 ≤ k
  k_ab : Pt
  k_ab_mem : k_ab ∈ [(24, 7), (17, 5), (10, 3), (3, 1)]
  k_ineq : (k + 1) * k_ab.2 < k_ab.1
  k_ne2 : k ≠ 2
  enP : Pt
  enP_eq : enP = (-(k : ℤ), 0)
  enQ : Pt
  enQ_eq : enQ = ((k + 1 : ℤ), 1)
  stP : Pt
  stP_eq : stP = (48, 14)
  stQ : Pt
  stQ_eq : stQ = (72, 21)
  dirE : Pt
  dirE_eq : dirE = (-2, 7)
  succP : Pt
  succP_eq : succP = (-2, 7)
  succQ : Pt
  succQ_eq : succQ = (-2, 7)
  hybrid_slip : HybridSlip828
  prop312_holds : Prop312_828

/-- `k = 1`: from the four `(a,b)` rows (each forces `k ≤ 2`) + `k ≠ 2`. -/
theorem k1_828 {H1 H2 : Prop} (h : Prop43Premises H1 H2) : h.k = 1 := by
  have hg1 := h.k_ge1
  have hn2 := h.k_ne2
  have hmem := h.k_ab_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with hab | hab | hab | hab
  · have h7 := h.k_ineq
    rw [hab] at h7
    dsimp only at h7
    rcases esquina_k12_247 h.k h.k_ge1 h7 with h1 | h2
    · exact h1
    · exact absurd h2 h.k_ne2
  · have h5 := h.k_ineq
    rw [hab] at h5
    dsimp only at h5
    omega
  · have h3 := h.k_ineq
    rw [hab] at h3
    dsimp only at h3
    omega
  · have h1 := h.k_ineq
    rw [hab] at h1
    dsimp only at h1
    exact esquina_k1_31 h.k h.k_ge1 h1

/-- The `φ₃` cut on the opaque lower-side list, case by case. -/
theorem cut_lower_828 {H1 H2 : Prop} (h : Prop43Premises H1 H2) :
    h.lowerP.map (cutPt (0, 1) (24, 7)) = [(-2, 0), (0, 0), (28, 8), (24, 7)] ∨
    h.lowerP.map (cutPt (0, 1) (24, 7)) = [(-3, 0), (0, 0), (28, 8), (24, 7)] ∨
    h.lowerP.map (cutPt (0, 1) (24, 7)) =
      [(-3, 0), (0, 0), (16, 4), (28, 8), (24, 7)] := by
  rcases h.lower_eq with h1 | h1 | h1
  · left; rw [h1]; exact cut_lower_828_a
  · right; left; rw [h1]; exact cut_lower_828_b
  · right; right; rw [h1]; exact cut_lower_828_c

/-- The pre-`φ` polygons assembled from the premise fields (cases (a)/(b)
    share one pair; case (c) adds the `(16,4)` vertex scaled). -/
def preP828ab {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enP, (48, 14), (56, 16)]

def preQ828ab {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enQ, (72, 21), (84, 24)]

def preP828c {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enP, (48, 14), (56, 16), (32, 8)]

def preQ828c {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enQ, (72, 21), (84, 24), (48, 12)]

/-- The top edge of the cut lower-side polygon, scaled: `(56,16) = 2·(28,8)`,
    `(48,14) = 2·(24,7)` (and the `Q` analogues `(84,24)`, `(72,21)`). -/
theorem pre828_top {H1 H2 : Prop} (h : Prop43Premises H1 H2) :
    (56, 16) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 2) ∧
    (48, 14) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 2) ∧
    (84, 24) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 3) ∧
    (72, 21) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 3) := by
  rcases cut_lower_828 h with h1 | h1 | h1 <;> rw [h1] <;> decide

/-- The case-(c) vertex `(16,4)`, scaled: `(32,8) = 2·(16,4)`,
    `(48,12) = 3·(16,4)`. -/
theorem pre828_c {H1 H2 : Prop} (h : Prop43Premises H1 H2)
    (hc : h.lowerP = [(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)]) :
    (32, 8) ∈ h.lowerP.map (scalePt 2) ∧ (48, 12) ∈ h.lowerP.map (scalePt 3) := by
  rw [hc]
  decide

/-- Proposition 4.3 (E7), CONDITIONAL: from the premise structure, one of the
    two final shapes holds (item (2) for cases (a)/(b), item (1) for case (c)),
    with Jacobian-factor pair `(−1,2)` (so `[φ(P),φ(Q)] = −[P,Q]·x²`, and with
    `[P,Q] = −1` after the swap this is `x²`). The ELIMINATION of the shapes
    is NOT part of this theorem (see the §E7 header note — it is already kernel).
    The polynomial-level statement is NOT claimed (Laurent layer, R14). -/
theorem prop43_conditional {H1 H2 : Prop} (h : Prop43Premises H1 H2) :
    ∃ finalP finalQ : List Pt,
      ((finalP = (preP828ab h).map (phiPow 4) ∧
        finalQ = (preQ828ab h).map (phiPow 4) ∧
        finalP = [(0, 0), (1, 0), (8, 14), (8, 16)] ∧
        finalQ = [(0, 0), (2, 1), (12, 21), (12, 24)]) ∨
       (finalP = (preP828c h).map (phiPow 4) ∧
        finalQ = (preQ828c h).map (phiPow 4) ∧
        finalP = [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)] ∧
        finalQ = [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)])) ∧
      phiJacPair 4 = (-1, 2) := by
  have hk : h.k = 1 := k1_828 h
  have henP : h.enP = (-1, 0) := by rw [h.enP_eq, hk]; decide
  have henQ : h.enQ = (2, 1) := by rw [h.enQ_eq, hk]; decide
  have _hcut := cut_lower_828 h
  have _htop := pre828_top h
  have _hpred := h.pred_mem
  have _hsucc : h.succP = (-2, 7) ∧ h.succQ = (-2, 7) := ⟨h.succP_eq, h.succQ_eq⟩
  rcases h.lower_eq with ha | hb | hc
  · -- Case (a): lower side `{(-2,0),(0,0),(28,8),(0,1)}` → item (2).
    refine ⟨(preP828ab h).map (phiPow 4), (preQ828ab h).map (phiPow 4),
      Or.inl ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_4⟩
    · show ([(0, 0), h.enP, (48, 14), (56, 16)] : List Pt).map (phiPow 4) =
        [(0, 0), (1, 0), (8, 14), (8, 16)]
      rw [henP]
      exact phi_828_abP
    · show ([(0, 0), h.enQ, (72, 21), (84, 24)] : List Pt).map (phiPow 4) =
        [(0, 0), (2, 1), (12, 21), (12, 24)]
      rw [henQ]
      exact phi_828_abQ
  · -- Case (b): lower side `{(-3,0),(0,0),(28,8),(0,1)}` → item (2).
    refine ⟨(preP828ab h).map (phiPow 4), (preQ828ab h).map (phiPow 4),
      Or.inl ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_4⟩
    · show ([(0, 0), h.enP, (48, 14), (56, 16)] : List Pt).map (phiPow 4) =
        [(0, 0), (1, 0), (8, 14), (8, 16)]
      rw [henP]
      exact phi_828_abP
    · show ([(0, 0), h.enQ, (72, 21), (84, 24)] : List Pt).map (phiPow 4) =
        [(0, 0), (2, 1), (12, 21), (12, 24)]
      rw [henQ]
      exact phi_828_abQ
  · -- Case (c): lower side with `(16,4)` → item (1).
    have _hc := pre828_c h hc
    refine ⟨(preP828c h).map (phiPow 4), (preQ828c h).map (phiPow 4),
      Or.inr ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_4⟩
    · show ([(0, 0), h.enP, (48, 14), (56, 16), (32, 8)] : List Pt).map (phiPow 4) =
        [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]
      rw [henP]
      exact phi_828_cP
    · show ([(0, 0), h.enQ, (72, 21), (84, 24), (48, 12)] : List Pt).map (phiPow 4) =
        [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]
      rw [henQ]
      exact phi_828_cQ


/-! ## §E8. Proposition 4.4, case (7,21) — kernel arithmetic.

The (7,21) case is a CLEAN F-fit (verified 2026-11-04): `en_{7,−2} F = (5/7)(7,21)`,
so `q = 7`. The proof is the shortest in §4: `φ₁` swap, Cor 7.4 (`q = 7`),
`φ₂` shear, `φ₃` final morphism. Only ONE premise field is needed (the `φ₂`-cut
link); everything else is kernel.

CORRECTION TO THE INVENTORY (verified while writing this file): the inventory
says the (7,21) F-side instance is "not yet a `Cor74Data` bundle" (inventory
§B, "still to add (i)"). That is STALE: `d1_cor74_2026-11-05.lean` ALREADY
defines `cor74_721` (direction `(7,−2)`, `(a/l,b) = (7,21)`, `en(F) = (5,15)`,
`q = 7`) with `cor74_721_cond3`, `cor74_721_exp_P/Q`, and proves
`ell721_normalization`. The bundle is re-pinned here self-contained
(`cor74_721_s4` + `ell721_normalization`, the latter copied with attribution
from `d1_cor74`), not claimed as new. -/

/-- The (7,21) base corners (TeX 1387): `{(0,0),(1,0),(7,21),(0,7)}`,
    multiplied by `(m,n) = (2,3)`. -/
def base721 : List Pt := [(0, 0), (1, 0), (7, 21), (0, 7)]

theorem swap_721 :
    base721.map swapPt = [(0, 0), (0, 1), (21, 7), (7, 0)] := by
  decide

/-- The (7,21) Cor 7.4 F-instance (Phase 1 `d1_cor74` `cor74_721`, re-pinned):
    `(ρ₀,σ₀) = (7,−2)` (pre-swap), `(a/l,b) = (7,21)`,
    `en(F) = (5,15) = (5/7)(7,21)`, `q = 7`. Condition (3) HOLDS (`b > a/l`). -/
def cor74_721_s4 : Cor74Data where
  dir := (7, -2)
  ab := (7, 21)
  p := 5
  q := 7
  hcop := by decide
  enF := (5, 15)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_721_s4_cond3 : cor74_721_s4.ab.2 > cor74_721_s4.ab.1 := by decide

theorem cor74_721_s4_exp_P : 7 * 2 = 14 := by decide

theorem cor74_721_s4_exp_Q : 7 * 3 = 21 := by decide

/-! ### The (7,21) ℓ-normalisation (support level).

Copied with attribution from `d1_cor74_2026-11-05.lean` (`mem_map_range_cast`,
`face721`, `text721`, `ell721_normalization`, `ell721_endpoints`, `ell721_cross`).
The paper's formula `ℓ_{1,−2}(P) = x^{28} λ_p (y − λ x^{−2})^{14}` is the
TEXT form; the true `(1,−2)`-face is the text support shifted by `x^{14}`
(the face's `st`-monomial `(14,0)`). The correct face is `λ_p · x^{14} · R^{14}`
with `R = x²y − λ` (the paper's `R` lacks an `x` factor — a genuine slip,
harmless for the polygon conclusion). The COEFFICIENT identity
`face = λ_p · x^{14} · R^{14}` (with binomial coefficients) is NOT proved here:
it needs the D2 polynomial layer (Leg E, R14). -/

/-- The true `(1,−2)`-face support: `{(14+2j, j) : 0 ≤ j ≤ 14}`. -/
def face721 : List Pt :=
  ((List.range 15).map Int.ofNat).map (fun a => (14 + 2 * a, a))

/-- The text formula's support: `{(28−2k, 14−k) : 0 ≤ k ≤ 14}`. -/
def text721 : List Pt :=
  ((List.range 15).map Int.ofNat).map (fun a => (28 - 2 * a, 14 - a))

/-- Membership in a range-map with a cast inside (Phase 1 `d1_cor74`, verbatim). -/
theorem mem_map_range_cast {n : ℕ} {F : ℤ → Pt} {e : Pt} :
    e ∈ ((List.range n).map Int.ofNat).map F ↔
      ∃ j : ℕ, j < n ∧ F (j : Int) = e := by
  constructor
  · intro h
    obtain ⟨a, ha, hax⟩ := List.mem_map.mp h
    obtain ⟨j, hj, hja⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hj
    exact ⟨j, hj, by rw [← hja] at hax; exact hax⟩
  · rintro ⟨j, hj, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(j : Int), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨j, by rw [List.mem_range]; exact hj, rfl⟩

/-- The ℓ-normalisation (Phase 1 `d1_cor74` `ell721_normalization`, verbatim):
    `e` is in the face iff `e − (14,0)` is in the text support. -/
theorem ell721_normalization (e : Pt) :
    e ∈ face721 ↔ (e.1 - 14, e.2) ∈ text721 := by
  simp only [face721, text721]
  rw [mem_map_range_cast, mem_map_range_cast]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨14 - j, by omega, ?_⟩
    apply Prod.ext <;> dsimp only <;> omega
  · rintro ⟨k, hk, h⟩
    have h1 : 28 - 2 * (k : Int) = e.1 - 14 := congrArg Prod.fst h
    have h2 : 14 - (k : Int) = e.2 := congrArg Prod.snd h
    refine ⟨14 - k, by omega, ?_⟩
    apply Prod.ext <;> dsimp only <;> omega

/-- Face/text endpoints + orientation (Phase 1 `d1_cor74`, verbatim). -/
theorem ell721_endpoints :
    (14, 0) ∈ face721 ∧ (42, 14) ∈ face721 ∧
    (0, 0) ∈ text721 ∧ (28, 14) ∈ text721 := by
  decide

theorem ell721_cross : 0 < crossProd (1, -2) ((42, 14) - (14, 0)) := by decide

/-! ### E8 φ-chain (TeX 1387–1396). -/

/-- `φ₂(x) = x, φ₂(y) = y + λx⁻²` cuts the `(7,0)` corner to `(−2,0)`
    (the `ℓ_{1,−2}` edge, `q = 7`, exponents `qm = 14`, `qn = 21`).
    Kernel computation on the model. -/
theorem cut_721 :
    ([(0, 0), (0, 1), (21, 7), (7, 0)] : List Pt).map (cutPt (7, 0) (-2, 0)) =
      [(0, 0), (0, 1), (21, 7), (-2, 0)] := by
  decide

/-- `φ₃(x) = x⁻¹, φ₃(y) = yx³` on the post-`φ₂` polygon. -/
theorem phi3_721 :
    ([(0, 0), (0, 1), (21, 7), (-2, 0)] : List Pt).map (phiPow 3) =
      [(0, 0), (3, 1), (0, 7), (2, 0)] := by
  decide

/-- Scaling the final base polygon by `(m,n) = (2,3)` (map order). -/
theorem scale2_721 :
    ([(0, 0), (3, 1), (0, 7), (2, 0)] : List Pt).map (scalePt 2) =
      [(0, 0), (6, 2), (0, 14), (4, 0)] := by
  decide

theorem scale3_721 :
    ([(0, 0), (3, 1), (0, 7), (2, 0)] : List Pt).map (scalePt 3) =
      [(0, 0), (9, 3), (0, 21), (6, 0)] := by
  decide

/-- The map-order lists are the paper's sets: `N(P) = {(0,0),2(2,0),2(3,1),2(0,7)}`
    i.e. `{(0,0),(4,0),(6,2),(0,14)}`; `N(Q) = {(0,0),3(2,0),3(3,1),3(0,7)}`
    i.e. `{(0,0),(6,0),(9,3),(0,21)}`. -/
theorem final721P_set (e : Pt) :
    e ∈ [(0, 0), (6, 2), (0, 14), (4, 0)] ↔ e ∈ [(0, 0), (4, 0), (6, 2), (0, 14)] := by
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

theorem final721Q_set (e : Pt) :
    e ∈ [(0, 0), (9, 3), (0, 21), (6, 0)] ↔ e ∈ [(0, 0), (6, 0), (9, 3), (0, 21)] := by
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

/-! ### E8 conditional theorem.

Premise fields (one):
- `afterPhi1_eq`: `φ₁` swap (kernel `swap_721`) — the post-`φ₁` polygon is
  `{(0,0),(7,0),(21,7),(0,1)}` (map order `[(0,0),(0,1),(21,7),(7,0)]`).
- `phi2cut`: Cor 7.4 (`q = 7`, `ℓ_{1,−2}(P) = x^{28}λ_p(y−λx^{−2})^{14}`,
  `ℓ_{1,−2}(Q) = x^{42}λ_q(y−λx^{−2})^{21}`) + `φ₂` — the shear cuts `(7,0)`
  to `(−2,0)`. The ℓ-form's SUPPORT content is kernel (`ell721_normalization`,
  with the `x¹⁴` correction); the coefficient identity is open (D2 layer).
The `φ₃` step and the scalings are kernel (`phi3_721`, `scale2_721`, `scale3_721`). -/

structure Prop44Premises where
  afterPhi1 : List Pt
  afterPhi1_eq : afterPhi1 = [(0, 0), (0, 1), (21, 7), (7, 0)]
  phi2cut : afterPhi1.map (cutPt (7, 0) (-2, 0)) = [(0, 0), (0, 1), (21, 7), (-2, 0)]

/-- The post-`φ₂` polygon, from the premise fields. -/
def postPhi2_721 (h : Prop44Premises) : List Pt :=
  h.afterPhi1.map (cutPt (7, 0) (-2, 0))

/-- The final base polygon, from the premise fields + the kernel `φ₃` map. -/
def final721base (h : Prop44Premises) : List Pt := (postPhi2_721 h).map (phiPow 3)

/-- Proposition 4.4 (E8), CONDITIONAL: from the premise structure, the final
    vertex lists are exactly the paper's (map order; set-equality with the
    paper's listing proved in `final721P_set`/`final721Q_set`), and the
    Jacobian-factor pair is `(−1,1)` (so `[φ₃(P),φ₃(Q)] = −[P,Q]·x`, and with
    `[P,Q] = −1` after the swap this is `x`). The polynomial-level statement
    is NOT claimed (Laurent layer, R14). The (7,21) row's elimination runs
    through E18 (§6) — and, independently, through §3 (E4). -/
theorem prop44_conditional (h : Prop44Premises) :
    ∃ finalP finalQ : List Pt,
      finalP = (final721base h).map (scalePt 2) ∧
      finalQ = (final721base h).map (scalePt 3) ∧
      finalP = [(0, 0), (6, 2), (0, 14), (4, 0)] ∧
      finalQ = [(0, 0), (9, 3), (0, 21), (6, 0)] ∧
      (∀ e : Pt, e ∈ finalP ↔ e ∈ [(0, 0), (4, 0), (6, 2), (0, 14)]) ∧
      (∀ e : Pt, e ∈ finalQ ↔ e ∈ [(0, 0), (6, 0), (9, 3), (0, 21)]) ∧
      phiJacPair 3 = (-1, 1) := by
  have e2 : postPhi2_721 h = [(0, 0), (0, 1), (21, 7), (-2, 0)] := h.phi2cut
  have e3 : final721base h = [(0, 0), (3, 1), (0, 7), (2, 0)] := by
    show (postPhi2_721 h).map (phiPow 3) = [(0, 0), (3, 1), (0, 7), (2, 0)]
    rw [e2]
    exact phi3_721
  have eP : (final721base h).map (scalePt 2) = [(0, 0), (6, 2), (0, 14), (4, 0)] := by
    rw [e3]
    exact scale2_721
  have eQ : (final721base h).map (scalePt 3) = [(0, 0), (9, 3), (0, 21), (6, 0)] := by
    rw [e3]
    exact scale3_721
  refine ⟨(final721base h).map (scalePt 2), (final721base h).map (scalePt 3),
    rfl, rfl, eP, eQ, ?_, ?_, phiJacPair_3⟩
  · intro e
    rw [eP]
    exact final721P_set e
  · intro e
    rw [eQ]
    exact final721Q_set e


/-! ## Verdict table (Leg B — CONFIRMED by the VM run, 2026-11-06:
FULL exit 0, 7 s, Lean 4.34.0; axiom lists below are the `#print axioms`
output of that run; second-tool Python check ALL PASS)

| Item | Verdict | Theorem(s) | Carried premises (named) |
|---|---|---|---|
| E5 Prop 4.1 (9,27) | CONDITIONAL | `prop41_conditional` | `Prop41Premises`: Cor 7.4 edge step, φ₃ edge step, Prop 8.2 applied instance |
| E6 Prop 4.2 (9,24) | CONDITIONAL | `prop42_conditional` | `Prop42Premises`: [GGV2] 3.12 soundness (`pred_sound`), [vdE] 10.2.6 (`pred_ne_25`), Prop 3.12(2) (`h312_2`), hybrid-vs-slip (`HybridSlip924`), φ₂ corners, edge transform, `(a',b')` dichotomy |
| E7 Prop 4.3 (8,28) | CONDITIONAL (reduction) | `prop43_conditional` | `Prop43Premises`: [GGV6] 2.5 (`pred_mem`), [GGV2] 3.12 setting (`prop312_holds`), hybrid-vs-slip (`HybridSlip828`), k=2 exclusion (`k_ne2`), lower-side shapes, Succ determination. ELIMINATION already KERNEL (see §E7 header) |
| E8 Prop 4.4 (7,21) | CONDITIONAL | `prop44_conditional` | `Prop44Premises`: Cor 7.4 (q=7) φ₂-cut link only |
| E9 Algorithm | KERNEL (implementation + output) | `psp_183`, `psp_183_dirs`, `psp_183_dirs_subset` | Correctness = [GGV2] Prop 3.12 (Leg F) — NOT claimed |
| E5 sieve | KERNEL | `sieve_table_927`, `sieve_derivation`, `sieve_rows_927` | — |
| E5/E7 k | KERNEL | `esquina_k1_927`, `esquina_k12_247`, `esquina_k1_31` | — |
| E5/E6/E7/E8 φ-maps + factors | KERNEL | `phi3_927P/Q`, `phi_924_sub*`, `phi_828_abP/Q`, `phi_828_cP/Q`, `phi3_721`, `phiJacPair_3/4` | — |
| E6/E7/E8 Cor 7.4 data | KERNEL (re-pinned) | `cor74_prop42_s4`, `cor74_prop43_s4`, `cor74_721_s4`, `cor74_927_s4` | — |
| E8 ℓ-normalisation | KERNEL (support level) | `ell721_normalization` | Coefficient identity `face = λ_p·x¹⁴·R¹⁴` OPEN (D2 layer) |

NOT proved here (correctly out of scope for this leg): the polynomial-level
existence statements (`P, Q ∈ L^{(1)}` with `[P,Q] = x`/`x²`) — Laurent layer
(R14, Leg E); the chain rule identifying `[φ(P),φ(Q)]` with the factor pair
(R14, Leg E); [GGV2] Prop 3.12, [GGV6] Prop 2.5, [vdE] Prop 10.2.6 themselves
(Leg F); the hybrid-vs-slip resolution (retrieval NOT FOUND 2026-11-06);
the (7,21) coefficient identity (D2 layer). No `sorryAx` anywhere in this file.
-/

#print axioms prop41_conditional
#print axioms prop42_conditional
#print axioms prop43_conditional
#print axioms prop44_conditional
#print axioms psp_183
#print axioms sieve_table_927
#print axioms ell721_normalization
#print axioms phiJacPair_3
#print axioms phiJacPair_4
/-
  GGHV §5 ("Systems of polynomial equations for (9,24) and (9,27)"), full-proof leg C.
  Paper: arXiv:2204.14178v1, TeX ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.
  Inventory: ~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/gghv_statement_inventory.md
  (entries E10–E17). Scratch deliverable — NO repo commits; incorporation only after the
  validation gate.

  CLAIM: see the per-item verdicts below. STATUS: compiled on lean-build-3 (Lean 4.34.0,
  Mathlib), axioms printed per theorem; no `sorryAx` anywhere in this file.
  Toolchain: Lean 4.34.0, Lake 5.0.0, Singular 4.3.1, SymPy 1.14.0 (all on lean-build-3).

  Per-item verdicts (HLRE v5 grades; KERNEL = kernel-verified on the permitted triple
  [propext, Classical.choice, Quot.sound] or a subset; CONDITIONAL = proved from the named
  premises; BLOCKED = not formalized, blocker stated):
  - E13 (f separable): KERNEL. ODE, C3*f = f1, f = y(y+1)g, deg f = 6, deg g = 4,
    g(0) ≠ 0, g(-1) ≠ 0, Bézout identity, separability — all kernel over ℚ[y].
    Second-tool check (SymPy 1.14.0 + Singular 4.3.1, both rc=0): e13_second_tool_check.log.
  - E16 (9 equations ⇒ principal equation): KERNEL (elimination step). The certificate
    identity is proved by `ring`; the principal equation follows from the 9 equations
    + d_{-1} ≠ 0. The DERIVATION of the 9 equations from the C/F/D expansions is OPEN
    (carried as the link hypothesis in E10's assembly).
  - E14 (D_k ∈ K[y]): CONDITIONAL (kernel induction from the convolution identity,
    carried as a hypothesis; the convolution identity itself is the E11 link).
  - E15 (valuations -39 / 51): kernel arithmetic identities + CONDITIONAL valuation
    bounds (from the E11-derived C_k bounds + monomial valuations, carried).
  - E12 (Remark): PARTIAL — the tilde identities are KERNEL; "(P̃,Q̃) still satisfy
    Thm 5.1" is CONDITIONAL on bracket/face preservation (named premises).
  - E11 (calculo de C): BLOCKED on the Laurent-series library (Mathlib has no ready
    Laurent series with the needed API). KERNEL pieces proved here: the corrected
    recursion step, and the sign-slip lemma showing the paper's as-printed recursion
    gives -P_{6-k} instead of P_{6-k}. The existence of C, F with items (1)–(4) is
    NOT formalized; it is carried as the link hypothesis in E10/E14/E15.
  - E10 (Theorem 5.1): CONDITIONAL assembly — kernel rescaling + endgame applied to
    the §5 data supplied by the link hypothesis (link_924/link_927, §5 rescaling inputs,
    coefficient-system derivation, 9-equation derivation, [GGV1] Props 1.13/2.1).
  - E17 (Corollary 5.2): CONDITIONAL assembly on Thm 5.1 + Cor 7.2 + Thm 2.6 + Def 4.3
    + the ψ sixth-power step (all carried inside the link hypothesis).

  Paper slips found in §5 (flagged, not silently corrected):
  (1) E11 recursion sign error (TeX ~1462–1465): the paper writes
      2C₃C_{3-k} = -P_{6-k} - Σ_{j=1}^{k-1} C_{3-j}C_{3-k+j}, but the expansion of
      (Σ_{i=0}^k C_{3-i}x^{3-i})² at x^{6-k} is 2C₃C_{3-k} + Σ_{j=1}^{k-1}…, which with
      the printed recursion equals -P_{6-k}, contradicting (a_k). Correct:
      C_{3-k} := (1/(2C₃))(P_{6-k} - Σ_{j=1}^{k-1}…). See e11_recursion_sign_slip.
  (2) E11 valuation estimates (TeX 1477, 1493): the paper writes v(C_{3-j}C_{3-k+j})
      ≤ v(C_{3-j}) v(C_{3-k+j}) (product of valuations); it should be the sum.
      The bounds that follow are the sum, so this is a harmless typo.
  (3) E16 (D̃²)_{-7} display (TeX ~1680): contains a literal term `2 d_{-1} 0`.
      Correct expansion (from the (D̃²)_{-k} definition, and as used in the Singular
      elim/cert scripts): 2 d₃d_{-10} + 2 d₂d_{-9} + 2 d₁d_{-8} + 2 d₀d_{-7}
      + 2 d_{-1}d_{-6} + 2 d_{-2}d_{-5} + 2 d_{-3}d_{-4} with d₃=1, d₂=0 (the printed
      term is a slip for the vanishing 2 d₂d_{-9} term). The 9-equation system used
      here is the correct expansion. §5 displays no (D̃²)_{-6} equation; the 9
      equations are 6 D̃² equations (-1,-2,-3,-4,-5,-7) + 3 Q̃ equations (-1,-2,-4).
-/

open Polynomial
open Finset

/-! ## §1. Helpers: `C`-coefficients against polynomial numerals.

  `ring` / `ring_nf` treat each `C r` as an opaque atom and do not combine
  `C a * C b`; `decide` fails on ℚ[X] equality; `native_decide` is forbidden
  (adds `Lean.ofReduceBool`). The lemmas below combine `C q * n → C (q*n)`
  (and the symmetric forms) so that `norm_num` can evaluate the rational
  arithmetic inside `C (…)`. Note: `rw [C_mul_ofNat']` works where
  `simp only [C_mul_ofNat']` does not fire, so the pipeline below uses
  `repeat rw`. -/

lemma C_mul_ofNat' (q : ℚ) (n : ℕ) [n.AtLeastTwo] :
    C q * (OfNat.ofNat n : ℚ[X]) = C (q * OfNat.ofNat n) := by
  rw [← C_ofNat, ← C_mul]

lemma ofNat_mul_C' (q : ℚ) (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℚ[X]) * C q = C (OfNat.ofNat n * q) := by
  rw [mul_comm, C_mul_ofNat']; congr 1; ring

lemma C_mul_natCast' (q : ℚ) (n : ℕ) :
    C q * ((n : ℕ) : ℚ[X]) = C (q * (n : ℚ)) := by
  rw [← map_natCast C, ← C_mul]

lemma natCast_mul_C' (q : ℚ) (n : ℕ) :
    ((n : ℕ) : ℚ[X]) * C q = C ((n : ℚ) * q) := by
  rw [mul_comm, C_mul_natCast']; congr 1; ring

/-- Monomial normalizers for the Bézout identity (probe32): `ring_nf` leaves
    monomials with two C-coefficients in several arrangements (C's adjacent or
    separated by X^n, left- or right-nested), and `ring` cannot add distinct
    C-atoms. These normalize every monomial to X^n * C r (single C, X first). -/
lemma C_mul_X_pow_mul_C (a b : ℚ) (n : ℕ) :
    C a * X ^ n * C b = C (a * b) * X ^ n := by
  have h : C a * X ^ n * C b = C a * C b * X ^ n := by ring
  rw [h, ← C_mul]

lemma X_pow_mul_C_mul_C (a b : ℚ) (n : ℕ) :
    X ^ n * C a * C b = X ^ n * C (a * b) := by
  have h : X ^ n * C a * C b = X ^ n * (C a * C b) := by ring
  rw [h, ← C_mul]

lemma C_mul_C_mul_X_pow (a b : ℚ) (n : ℕ) :
    C a * (C b * X ^ n) = C (a * b) * X ^ n := by
  have h : C a * (C b * X ^ n) = (C a * C b) * X ^ n := by ring
  rw [h, ← C_mul]

lemma C_mul_X_pow (a : ℚ) (n : ℕ) : C a * X ^ n = X ^ n * C a := mul_comm _ _

lemma C_mul_X_pow_C (a b : ℚ) (n : ℕ) :
    C a * (X ^ n * C b) = X ^ n * C (a * b) := by
  have h : C a * (X ^ n * C b) = C a * C b * X ^ n := by ring
  rw [h, ← C_mul, C_mul_X_pow]

/-! ## §2. E13 — `f` separable (KERNEL).

  Definitions (all in ℚ[X], coefficients as `C (r : ℚ)`):
  C₃ = y⁸(y+1); f₁ = -(1/910) y⁹(y+1)²(35 - 42y + 54y² - 81y³ + 243y⁴);
  g = -(1/910)(35 - 42y + 54y² - 81y³ + 243y⁴);
  f = -(243/910)y⁶ - (81/455)y⁵ + (27/910)y⁴ - (6/455)y³ + (1/130)y² - (1/26)y.
  Bézout coefficients U, V from the SymPy `gcdex` check (see e13_second_tool_check.log).
  Pipeline for the polynomial identities (verified on the ODE, probe25):
  simp only [defs + derivative lemmas + C-combine lemmas] → norm_num → ring_nf →
  simp only [mul_assoc] → repeat rw [C_mul_ofNat'] → repeat rw [ofNat_mul_C'] →
  repeat rw [C_mul_natCast'] → repeat rw [natCast_mul_C'] → norm_num →
  simp only [C_ofNat, map_one] → ring. -/

noncomputable def e13C3 : ℚ[X] := X ^ 8 * (X + 1)

noncomputable def e13f1 : ℚ[X] := C (-(1 / 910)) * X ^ 9 * (X + 1) ^ 2 *
  (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4)

noncomputable def e13g : ℚ[X] := C (-(1 / 910)) *
  (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4)

noncomputable def e13f : ℚ[X] := C (-(243 / 910)) * X ^ 6 - C (81 / 455) * X ^ 5
  + C (27 / 910) * X ^ 4 - C (6 / 455) * X ^ 3 + C (1 / 130) * X ^ 2 - C (1 / 26) * X

noncomputable def e13U : ℚ[X] := C (600696 / 455) * X ^ 4 + C (339552 / 455) * X ^ 3
  - C (47088 / 455) * X ^ 2 + C (16992 / 455) * X - C (1112 / 65)

noncomputable def e13V : ℚ[X] := -(C (100116 / 455) * X ^ 5) - C (67716 / 455) * X ^ 4
  + C (11448 / 455) * X ^ 3 - C (1032 / 91) * X ^ 2 + C (436 / 65) * X - C 26

/-- E13: derivative of C₃. -/
theorem e13_C3_deriv : derivative e13C3 = (9 * X + 8) * X ^ 7 := by
  simp only [e13C3, derivative_mul, derivative_pow, derivative_add, derivative_X,
    derivative_one, derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul,
    ← mul_add, ← C_add, map_neg, map_one]
  norm_num
  ring_nf

/-- E13: the differential equation for f₁. -/
theorem e13_ode : X ^ 9 * (X + 1) ^ 2
    = 6 * X * (X + 1) * derivative e13f1 - 10 * (9 * X + 8) * e13f1 := by
  simp only [e13C3, e13f1, e13f, e13g, e13U, e13V, derivative_mul, derivative_pow,
    derivative_add, derivative_sub, derivative_C, derivative_X, derivative_one,
    derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul, ← mul_add, ← C_add,
    map_neg, map_one]
  norm_num
  ring_nf
  simp only [mul_assoc]
  repeat rw [C_mul_ofNat']
  repeat rw [ofNat_mul_C']
  repeat rw [C_mul_natCast']
  repeat rw [natCast_mul_C']
  norm_num
  try simp only [C_ofNat, map_one]
  ring

/-- E13: f = y(y+1)g. -/
theorem e13_f_factor : e13f = X * (X + 1) * e13g := by
  simp only [e13C3, e13f1, e13f, e13g, e13U, e13V, derivative_mul, derivative_pow,
    derivative_add, derivative_sub, derivative_C, derivative_X, derivative_one,
    derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul, ← mul_add, ← C_add,
    map_neg, map_one]
  norm_num
  ring_nf
  simp only [mul_assoc]
  repeat rw [C_mul_ofNat']
  repeat rw [ofNat_mul_C']
  repeat rw [C_mul_natCast']
  repeat rw [natCast_mul_C']
  norm_num
  try simp only [C_ofNat, map_one]
  ring

/-- E13: C₃·f = f₁ (so f = C₃²F_{-4} with C₃ = y⁸(y+1)).
    Proved in factored form via `e13_f_factor`: both sides are the same product
    of atoms, so `ring` closes it with no coefficient arithmetic. -/
theorem e13_C3_mul_f : e13C3 * e13f = e13f1 := by
  rw [e13_f_factor]
  simp only [e13C3, e13g, e13f1]
  ring


/-- E13: deg f = 6. -/
theorem e13_f_natDegree : e13f.natDegree = 6 := by
  unfold e13f
  compute_degree <;> norm_num

/-- E13: deg g = 4. (The outer `C (-(1/910))` factor defeats `compute_degree`
    directly, so split it off with `natDegree_mul` and compute the inner degree.) -/
theorem e13_g_natDegree : e13g.natDegree = 4 := by
  have h1 : (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4 : ℚ[X]).natDegree
      = 4 := by
    compute_degree <;> norm_num
  have hne : (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4 : ℚ[X]) ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  unfold e13g
  rw [Polynomial.natDegree_mul (C_ne_zero.mpr (by norm_num)) hne, h1,
    Polynomial.natDegree_C]

/-- E13: g(0) = -1/26 ≠ 0. -/
theorem e13_g_ne_zero_at_zero : eval 0 e13g ≠ 0 := by
  unfold e13g
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X]
  norm_num

/-- E13: g(-1) = -1/2 ≠ 0 (so (y+1) ∤ g). -/
theorem e13_g_ne_zero_at_neg_one : eval (-1) e13g ≠ 0 := by
  unfold e13g
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X]
  norm_num

/-- E13: Bézout identity U·f + V·f′ = 1 (coefficients from SymPy `gcdex`). -/
theorem e13_bezout : e13U * e13f + e13V * derivative e13f = 1 := by
  simp only [e13C3, e13f1, e13f, e13g, e13U, e13V, derivative_mul, derivative_pow,
    derivative_add, derivative_sub, derivative_C, derivative_X, derivative_one,
    derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul, ← mul_add, ← C_add,
    map_neg, map_one]
  norm_num
  ring_nf
  simp only [mul_assoc]
  repeat rw [C_mul_ofNat']
  repeat rw [ofNat_mul_C']
  repeat rw [C_mul_natCast']
  repeat rw [natCast_mul_C']
  norm_num
  -- Combine the C-coefficients (probe32): `ring_nf` leaves products `C a * C b`
  -- and sums of like monomials with different C-coefficients, which `ring`
  -- treats as distinct atoms. First normalize every monomial to X^n * C r,
  -- turn subtractions into additions of negations, push the negation inside C,
  -- right-associate the sum, then factor out the common X-power and combine the
  -- C's (C is a ring hom). `ring_nf` then cancels the identical-atom pairs
  -- (each X^5..X^10 monomial appears twice with the same C-atom and opposite
  -- signs, the U·f and V·f′ contributions); only the X^1 terms (distinct
  -- C-atoms) survive, and a second combining pass finishes them (`ring_nf`
  -- leaves the goal in HSub form, so `← mul_sub`/`← C_sub` do the work).
  simp only [C_mul_X_pow_mul_C, X_pow_mul_C_mul_C, C_mul_C_mul_X_pow, C_mul_X_pow_C,
    ← C_mul, C_mul_X_pow]
  simp only [sub_eq_add_neg, ← mul_neg, ← map_neg]
  simp only [add_assoc, ← mul_add, ← mul_sub, ← C_add, ← C_sub]
  norm_num
  ring_nf
  simp only [C_mul_X_pow, ← mul_neg, ← map_neg, ← mul_add, ← mul_sub, ← C_add,
    ← C_sub]
  norm_num
  try ring

/-- E13: f is separable. -/
theorem e13_f_separable : e13f.Separable := by
  rw [Polynomial.separable_def']
  exact ⟨e13U, e13V, e13_bezout⟩

/-! ## §3. E16 — the 9-equation system implies the principal equation (KERNEL).

  The certificate identity below is transcribed verbatim from
  `d1_singular_cert_s5_2026-11-05.sing` (Singular verifies CERT_DIFF = 0).
  The 9 equations are the 6 D̃² equations (-1,-2,-3,-4,-5,-7) + the 3 Q̃ equations
  (-1,-2,-4), in the CORRECT expansion (see the (D̃²)_{-7} slip note in the header).
  The derivation of the 9 equations from the C/F/D expansions is OPEN — only the
  elimination step (9 equations ⇒ principal equation) is proved here. -/

/-- E16 certificate identity: d_{-1} * (principal equation) = combination of the
    9 equations. Proved by `ring` (integer coefficients, no `C`'s). -/
theorem e16_cert {R : Type*} [CommRing R]
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F : R) :
    dm1 * (18 * C3 ^ 23 * F * d1 * dm1 ^ 6 + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9)
    = (-12 * C3 ^ 46 * F ^ 2 * d0 ^ 2 * dm1 - 12 * C3 ^ 46 * F ^ 2 * d1 * dm1 ^ 2
        - 12 * C3 ^ 46 * F ^ 2 * dm1 * dm3 - 18 * C3 ^ 23 * F * d0 ^ 2 * dm1 ^ 3 * dm2
        - 18 * C3 ^ 23 * F * d1 * dm1 ^ 4 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 * dm3
        - 27 * d0 ^ 2 * d1 * dm1 ^ 7 - 27 * d0 ^ 2 * dm1 ^ 5 * dm2 ^ 2
        - 27 * d0 * dm1 ^ 7 * dm2 - 27 * d1 ^ 2 * dm1 ^ 8 - 27 * d1 * dm1 ^ 7 * dm3
        - 27 * d1 * dm1 ^ 6 * dm2 ^ 2 + 27 * dm1 ^ 9 - 27 * dm1 ^ 5 * dm2 ^ 2 * dm3)
      * (2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4)
    + (-24 * C3 ^ 46 * F ^ 2 * d0 * d1 * dm1 - 12 * C3 ^ 46 * F ^ 2 * dm1 * dm2
        - 36 * C3 ^ 23 * F * d0 * d1 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 ^ 2
        - 54 * d0 * d1 ^ 2 * dm1 ^ 7 - 54 * d0 * d1 * dm1 ^ 5 * dm2 ^ 2
        + 27 * d0 * dm1 ^ 8 - 54 * d1 * dm1 ^ 7 * dm2 - 27 * dm1 ^ 5 * dm2 ^ 3)
      * (dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5)
    + (-12 * C3 ^ 46 * F ^ 2 * d1 ^ 2 * dm1 - 12 * C3 ^ 46 * F ^ 2 * dm1 ^ 2
        - 18 * C3 ^ 23 * F * d1 ^ 2 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 4 * dm2
        - 27 * d1 ^ 3 * dm1 ^ 7 - 27 * d1 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 27 * dm1 ^ 6 * dm2 ^ 2)
      * (2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6)
    + (-24 * C3 ^ 46 * F ^ 2 * d0 * dm1 - 36 * C3 ^ 23 * F * d0 * dm1 ^ 3 * dm2
        - 54 * d0 * d1 * dm1 ^ 7 - 54 * d0 * dm1 ^ 5 * dm2 ^ 2 - 27 * dm1 ^ 7 * dm2)
      * (dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7)
    + (-24 * C3 ^ 46 * F ^ 2 * d1 * dm1 - 36 * C3 ^ 23 * F * d1 * dm1 ^ 3 * dm2
        - 54 * d1 ^ 2 * dm1 ^ 7 - 54 * d1 * dm1 ^ 5 * dm2 ^ 2 + 27 * dm1 ^ 8)
      * (2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8)
    + (-12 * C3 ^ 46 * F ^ 2 * dm1 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2
        - 27 * d1 * dm1 ^ 7 - 27 * dm1 ^ 5 * dm2 ^ 2)
      * (2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7
        + 2 * d1 * dm8)
    + (8 * C3 ^ 46 * F ^ 2 * d0 * dm1 + 12 * C3 ^ 23 * F * d0 * dm1 ^ 3 * dm2
        + 18 * d0 * d1 * dm1 ^ 7 + 18 * d0 * dm1 ^ 5 * dm2 ^ 2 + 18 * dm1 ^ 7 * dm2)
      * (3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2
        + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7)
    + (8 * C3 ^ 46 * F ^ 2 * d1 * dm1 + 12 * C3 ^ 23 * F * d1 * dm1 ^ 3 * dm2
        + 18 * d1 ^ 2 * dm1 ^ 7 + 18 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * dm1 ^ 8)
      * (3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3
        + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6
        + 3 * dm8)
    + (8 * C3 ^ 46 * F ^ 2 * dm1 + 12 * C3 ^ 23 * F * dm1 ^ 3 * dm2
        + 18 * d1 * dm1 ^ 7 + 18 * dm1 ^ 5 * dm2 ^ 2)
      * (3 * dm10 + 3 * dm1 ^ 2 * dm2 + 3 * d0 * dm2 ^ 2 + 6 * d0 * dm1 * dm3
        + 6 * d1 * dm2 * dm3 + 3 * d0 ^ 2 * dm4 + 6 * d1 * dm1 * dm4 + 6 * dm3 * dm4
        + 6 * d0 * d1 * dm5 + 6 * dm2 * dm5 + 3 * d1 ^ 2 * dm6 + 6 * dm1 * dm6
        + 6 * d0 * dm7 + 6 * d1 * dm8 + F * C3 ^ 23) := by
  ring

/-- E16 principal equation (kernel): from the 9 equations and d_{-1} ≠ 0. -/
theorem e16_principal {R : Type*} [Field R]
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F : R)
    (hD1 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD2 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD3 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD4 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD5 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD7 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7
      + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2
      + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3
      + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6
      + 3 * dm8 = 0)
    (hQ4 : 3 * dm10 + 3 * dm1 ^ 2 * dm2 + 3 * d0 * dm2 ^ 2 + 6 * d0 * dm1 * dm3
      + 6 * d1 * dm2 * dm3 + 3 * d0 ^ 2 * dm4 + 6 * d1 * dm1 * dm4 + 6 * dm3 * dm4
      + 6 * d0 * d1 * dm5 + 6 * dm2 * dm5 + 3 * d1 ^ 2 * dm6 + 6 * dm1 * dm6
      + 6 * d0 * dm7 + 6 * d1 * dm8 + F * C3 ^ 23 = 0)
    (hdm1 : dm1 ≠ 0) :
    18 * C3 ^ 23 * F * d1 * dm1 ^ 6 + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9 = 0 := by
  have h := e16_cert d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F
  rw [hD1, hD2, hD3, hD4, hD5, hD7, hQ1, hQ2, hQ4] at h
  simp only [mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hdm1

/-! ## §4. E14 — D_k ∈ K[y] (CONDITIONAL).

  ℕ-indexed from the top: D_{2-n} = c n * C3^(2n+1) with only natural exponents.
  The convolution identity `p n = 2*C3*c n + Σ_{m<n} c m * c (n-1-m)` is the
  C² = P coefficient relation, carried as a hypothesis (its proof from E11(1) is
  the E11 link). S is the subring of K playing the role of K[y]; (1/2 : K) ∈ S is
  needed since the recurrence divides by 2. -/

theorem e14_d_mem {K : Type*} [Field K] [CharZero K] {S : Subring K}
    (hhalf : (1 / 2 : K) ∈ S) (C3 : K) (hC3 : C3 ∈ S) (c p : ℕ → K)
    (hp : ∀ n, p n ∈ S)
    (hconv : ∀ n, p n = 2 * C3 * c n + ∑ m ∈ Finset.range n, c m * c (n - 1 - m))
    (n : ℕ) : (c n * C3 ^ (2 * n + 1)) ∈ S := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key : p n * C3 ^ (2 * n)
        = 2 * (c n * C3 ^ (2 * n + 1))
          + ∑ m ∈ Finset.range n,
            (c m * C3 ^ (2 * m + 1)) * (c (n - 1 - m) * C3 ^ (2 * (n - 1 - m) + 1)) := by
      rw [hconv n, add_mul, Finset.sum_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro m hm
        have hm' : m < n := Finset.mem_range.mp hm
        have hexp : 2 * m + 1 + (2 * (n - 1 - m) + 1) = 2 * n := by omega
        have hC3pow : C3 ^ (2 * n) = C3 ^ (2 * m + 1) * C3 ^ (2 * (n - 1 - m) + 1) := by
          rw [← pow_add, hexp]
        rw [hC3pow]
        ring
    have hsum : (∑ m ∈ Finset.range n,
        (c m * C3 ^ (2 * m + 1)) * (c (n - 1 - m) * C3 ^ (2 * (n - 1 - m) + 1))) ∈ S := by
      apply sum_mem
      intro m hm
      have hm' : m < n := Finset.mem_range.mp hm
      apply S.mul_mem
      · exact ih m hm'
      · exact ih (n - 1 - m) (by omega)
    have hpn : p n * C3 ^ (2 * n) ∈ S := S.mul_mem (hp n) (S.pow_mem hC3 _)
    have hd : c n * C3 ^ (2 * n + 1)
        = (1 / 2 : K) * (p n * C3 ^ (2 * n)
          - ∑ m ∈ Finset.range n,
            (c m * C3 ^ (2 * m + 1)) * (c (n - 1 - m) * C3 ^ (2 * (n - 1 - m) + 1))) := by
      rw [key]
      ring
    rw [hd]
    apply S.mul_mem hhalf
    exact S.sub_mem hpn hsum

/-! ## §5. E15 — valuations v_{-13,-1}(D) = -39, v_{17,1}(D) = 51.

  Kernel arithmetic identities (the paper's TeX 1707–1710 and 1721–1724) plus
  CONDITIONAL valuation bounds: an abstract directed valuation `v` (the properties
  of v_{ρ,σ} the argument uses), the E11-derived C_k bounds, and the x-monomial
  valuations (passed as explicit ℤ hypotheses, since the x-monomials live in the
  Laurent ring, not in R). The paper's v_{ρ,σ} is the MAXIMUM over monomials
  (the (ρ,σ)-degree), which is what makes v(C₃) = -8 resp. 9. -/

/-- Abstract directed valuation (the properties of v_{ρ,σ} that E15's argument uses). -/
structure ValData (R : Type*) [CommRing R] where
  v : R → ℤ
  v_one : v 1 = 0
  v_mul : ∀ a b, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b

theorem pow_ne_zero_of_ne {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (a : R) (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_ne_zero
  | succ n ih => rw [pow_succ]; exact mul_ne_zero ih ha

theorem val_pow {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R] (V : ValData R)
    (a : R) (n : ℕ) (ha : a ≠ 0) :
    V.v (a ^ n) = (n : ℤ) * V.v a := by
  induction n with
  | zero => rw [pow_zero, V.v_one]; simp
  | succ n ih =>
    rw [pow_succ, V.v_mul _ _ (pow_ne_zero_of_ne a ha n) ha, ih]
    push_cast
    ring

/-- E15 arithmetic identity (kernel): the (-13,-1) bound is constant in k. -/
theorem e15_arith_neg13 (k : ℤ) : -16 * k + 1 + (5 - 2 * k) * (-8) = -39 := by ring

/-- E15 arithmetic identity (kernel): the (17,1) bound is constant in k. -/
theorem e15_arith_17 (k : ℤ) : 18 * k + 6 + (5 - 2 * k) * 9 = 51 := by ring

/-- E15 (-13,-1) bound (conditional): in ℕ-indexed form (k = 2 - n), if the
    C-coefficient bound v(C_{2-n}) ≤ 3n - 5 (from E11(3): lowest y-power of C_k
    is ≥ y^{3k-1}), v(C3) = -8, and the x-monomial contributes hxv = 13n - 26,
    then v(D_{2-n} x^{2-n}) ≤ -39. -/
theorem e15_bound_neg13 {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (V : ValData R)
    (C3 : R) (c : ℕ → R) (n : ℕ)
    (hC3 : C3 ≠ 0) (hC3v : V.v C3 = -8)
    (hcn : c n ≠ 0)
    (hC : V.v (c n) ≤ 3 * (n : ℤ) - 5)
    (hxv : ℤ) (hhxv : hxv = 13 * (n : ℤ) - 26) :
    V.v (c n * C3 ^ (2 * n + 1)) + hxv ≤ -39 := by
  have h1 : V.v (c n * C3 ^ (2 * n + 1))
      = V.v (c n) + (2 * (n : ℤ) + 1) * V.v C3 := by
    rw [V.v_mul _ _ hcn (pow_ne_zero_of_ne C3 hC3 _), val_pow V C3 _ hC3]
    push_cast
    ring
  rw [h1, hC3v, hhxv]
  omega

/-- E15 (17,1) bound (conditional): if v(C_{2-n}) ≤ 8 - n (from E11(4): highest
    y-power of C_k is ≤ y^{k+6}), v(C3) = 9, and the x-monomial contributes
    hxv = 34 - 17n, then v(D_{2-n} x^{2-n}) ≤ 51. -/
theorem e15_bound_17 {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (V : ValData R)
    (C3 : R) (c : ℕ → R) (n : ℕ)
    (hC3 : C3 ≠ 0) (hC3v : V.v C3 = 9)
    (hcn : c n ≠ 0)
    (hC : V.v (c n) ≤ 8 - (n : ℤ))
    (hxv : ℤ) (hhxv : hxv = 34 - 17 * (n : ℤ)) :
    V.v (c n * C3 ^ (2 * n + 1)) + hxv ≤ 51 := by
  have h1 : V.v (c n * C3 ^ (2 * n + 1))
      = V.v (c n) + (2 * (n : ℤ) + 1) * V.v C3 := by
    rw [V.v_mul _ _ hcn (pow_ne_zero_of_ne C3 hC3 _), val_pow V C3 _ hC3]
    push_cast
    ring
  rw [h1, hC3v, hhxv]
  omega

/-! ## §6. E12 — Remark (PARTIAL).

  The tilde transformation: P̃ = P + (2/3)α₁, Q̃ = Q - α₂P - α₀, with
  P = C² and Q = C³ + α₂C² + α₁C + α₀ + α_{-1}C⁻¹ + F. The two algebraic
  identities are KERNEL; the claim that (P̃,Q̃) still satisfy Thm 5.1 is
  CONDITIONAL on bracket preservation and face preservation (named premises
  `hJac`, `hFace` — the bracket computation and the vertex check are not
  formalized here). -/

/-- E12: Q̃ = C³ + α₁C + λC⁻¹ + F with λ := α_{-1} (kernel, pure `ring`). -/
theorem e12_Qtilde {K : Type*} [Field K] [CharZero K] {C F α2 α1 α0 αm1 : K}
    {P Q : K} (hP : P = C ^ 2)
    (hQ : Q = C ^ 3 + α2 * C ^ 2 + α1 * C + α0 + αm1 * C⁻¹ + F) :
    (Q - α2 * P - α0) = C ^ 3 + α1 * C + αm1 * C⁻¹ + F := by
  rw [hQ, hP]; ring

/-- E12: the first correction to C̃² (kernel). -/
theorem e12_Ctilde_sq {K : Type*} [Field K] [CharZero K] {C α1 : K} (hC : C ≠ 0) {P : K}
    (hP : P = C ^ 2) :
    (C + (1 / 3) * α1 * C⁻¹) ^ 2
      = (P + (2 / 3) * α1) + (α1 ^ 2 / 9) * C⁻¹ ^ 2 := by
  rw [hP]; field_simp; ring

/-- E12 Remark, conditional: the tilde pair has Q̃ in the required form (with
    λ = α_{-1}) and satisfies Thm 5.1's conditions, given bracket preservation
    (`hJac`) and face preservation (`hFace`). -/
theorem e12_remark_conditional {K : Type*} [Field K] [CharZero K]
    {C F α2 α1 α0 αm1 : K} (hC : C ≠ 0)
    {P Q : K} (hP : P = C ^ 2)
    (hQ : Q = C ^ 3 + α2 * C ^ 2 + α1 * C + α0 + αm1 * C⁻¹ + F)
    (JacCond FaceCond : K → K → Prop)
    (hJac : JacCond (P + (2 / 3) * α1) (Q - α2 * P - α0))
    (hFace : FaceCond (P + (2 / 3) * α1) (Q - α2 * P - α0)) :
    ∃ lam : K, (Q - α2 * P - α0) = C ^ 3 + α1 * C + lam * C⁻¹ + F
      ∧ JacCond (P + (2 / 3) * α1) (Q - α2 * P - α0)
      ∧ FaceCond (P + (2 / 3) * α1) (Q - α2 * P - α0) := by
  refine ⟨αm1, ?_, hJac, hFace⟩
  exact e12_Qtilde hP hQ

/-! ## §7. E11 — calculo de C (BLOCKED on the Laurent-series library).

  The Laurent series C, F and items (1)–(4) of Proposition `calculo de C` are NOT
  formalized: Mathlib has no ready Laurent series with the needed API (a D2
  INTERFACE gap). What IS proved here, kernel, is the recursion algebra:
  with c j := C_{3-j} and p k := P_{6-k}, the CORRECTED recursion yields the
  coefficient identity Σ_{j=0}^k C_{3-j}C_{3-k+j} = P_{6-k}, while the paper's
  AS-PRINTED recursion yields -P_{6-k} (a genuine sign error, TeX ~1462–1465).
  The valuation estimates' product-vs-sum typo (TeX 1477, 1493) is also flagged
  in the header; the corrected bounds are the E15 arithmetic (kernel). -/

/-- E11 recursion step (kernel, corrected sign). -/
theorem e11_recursion_step {R : Type*} [Field R] [CharZero R] {C3 : R} (hC3 : C3 ≠ 0)
    (c p : ℕ → R) (k : ℕ) (hk : 1 ≤ k) (hc0 : c 0 = C3)
    (hrec : c k = (2 * C3)⁻¹ * (p k - ∑ j ∈ Finset.range (k - 1), c (j + 1) * c (k - 1 - j))) :
    ∑ j ∈ Finset.range (k + 1), c j * c (k - j) = p k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrec
  have h2C3 : (2 * C3 : R) ≠ 0 := mul_ne_zero two_ne_zero hC3
  have hsplit : ∑ j ∈ Finset.range (k' + 1 + 1), c j * c (k' + 1 - j)
      = c 0 * c (k' + 1) + (∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))
        + c (k' + 1) * c 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.sub_self]
    rw [add_comm (∑ j ∈ Finset.range k', c (j + 1) * c (k' + 1 - (j + 1))) (c 0 * c (k' + 1))]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hij : k' + 1 - (j + 1) = k' - j := by omega
    rw [hij]
  have key : (2 * C3) * ((2 * C3)⁻¹
      * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j)))
      = p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j) := by
    rw [← mul_assoc, mul_inv_cancel₀ h2C3, one_mul]
  have h2 : C3 * ((2 * C3)⁻¹
        * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j)))
      + ((2 * C3)⁻¹
        * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))) * C3
      = p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j) := by
    have h3 : C3 * ((2 * C3)⁻¹
          * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j)))
        + ((2 * C3)⁻¹
          * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))) * C3
        = (2 * C3) * ((2 * C3)⁻¹
          * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))) := by ring
    rw [h3, key]
  rw [hsplit, hc0, hrec]
  linear_combination h2

/-- E11 sign slip (kernel): the paper's as-printed recursion yields -P_{6-k}. -/
theorem e11_recursion_sign_slip {R : Type*} [Field R] [CharZero R] {C3 : R} (hC3 : C3 ≠ 0)
    (c p : ℕ → R) (k : ℕ) (hk : 1 ≤ k) (hc0 : c 0 = C3)
    (hrec : c k = -(2 * C3)⁻¹ * (p k + ∑ j ∈ Finset.range (k - 1), c (j + 1) * c (k - 1 - j))) :
    ∑ j ∈ Finset.range (k + 1), c j * c (k - j) = -(p k) := by
  have hrec' : c k = (2 * C3)⁻¹
      * ((-p k) - ∑ j ∈ Finset.range (k - 1), c (j + 1) * c (k - 1 - j)) := by
    rw [hrec]; ring
  exact e11_recursion_step hC3 c (fun n => -p n) k hk hc0 hrec'

/-! ## §8. E10 — Theorem 5.1 (CONDITIONAL assembly).

  Kernel pieces proved here: the clearing lemma (principal equation ⇒ cleared
  form, general commutative ring), the rescaling lemma (cleared equation ⇒ nueva
  ecuacion principal, by factoring y^507(y+1)^6), the tilde-degree bound, and the
  endgame (nueva equation + d̃_{-1} = (y+1)^k + degree bounds + g(-1) ≠ 0 ⇒ False,
  splitting k ≥ 8 by divisibility vs k ≤ 7 by degrees).
  The assembly `thm51_conditional` applies these kernel lemmas to the §5 data
  supplied by the link hypothesis; the link's proof is the open part
  (link_924 / link_927, §5 rescaling inputs, coefficient-system derivation,
  9-equation derivation, [GGV1] Props 1.13/2.1). The g-facts are NOT part of the
  link: they are the kernel E13 results, transported here by cancelling y(y+1). -/

/-- E10 clearing lemma (kernel, general commutative ring): multiplying the principal
    equation by C3^6 and using C3^2 * F = f gives the cleared (all-polynomial) form.
    The step from the paper's F_{-4} (in K[y, C3^{-1}]) to this cleared form is the
    one carried piece here; the algebra below is kernel. -/
theorem e10_clearing {R : Type*} [CommRing R] {C3 F f d1 dm1 d0 : R}
    (hF : C3 ^ 2 * F = f) :
    C3 ^ 6 * (18 * C3 ^ 23 * d1 * dm1 ^ 6 * F + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9)
      = 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3 + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by
  have e1 : C3 ^ 29 * F = C3 ^ 27 * f := by rw [← hF]; ring
  have e3 : C3 ^ 75 * F ^ 3 = C3 ^ 69 * f ^ 3 := by rw [← hF]; ring
  calc C3 ^ 6 * (18 * C3 ^ 23 * d1 * dm1 ^ 6 * F + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9)
      = 18 * (C3 ^ 29 * F) * d1 * dm1 ^ 6 + 8 * (C3 ^ 75 * F ^ 3)
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by ring
    _ = 18 * (C3 ^ 27 * f) * d1 * dm1 ^ 6 + 8 * (C3 ^ 69 * f ^ 3)
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by rw [e1, e3]
    _ = 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by ring

-- The rescaling `ring` (degree-555 identity) needs more recursion depth / heartbeats.
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- E10 rescaling lemma (kernel over ℚ[y]): from the cleared principal equation and the
    substitutions C3 = y^8(y+1), f = y(y+1)g, d1 = y^26 d̃1, d0 = y^39 d̃0,
    d_{-1} = y^52 d̃_{-1}, derive the nueva ecuacion principal by factoring out
    y^507 (y+1)^6 (a non-zero polynomial, so cancellation is valid). -/
theorem e10_rescaling (C3 f d1 d0 dm1 dt1 dt0 dtm1 g : ℚ[X])
    (hC3 : C3 = X ^ 8 * (X + 1)) (hf : f = X * (X + 1) * g)
    (hd1 : d1 = X ^ 26 * dt1) (hd0 : d0 = X ^ 39 * dt0) (hdm1 : dm1 = X ^ 52 * dtm1)
    (hprinc : 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
      + 27 * C3 ^ 6 * d0 * dm1 ^ 9 = 0) :
    18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 8 * (X + 1) ^ 66 * g ^ 3
      + 27 * dt0 * dtm1 ^ 9 = 0 := by
  have hfac : 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9
      = X ^ 555 * (X + 1) ^ 6 * (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g
        + 8 * (X + 1) ^ 66 * g ^ 3 + 27 * dt0 * dtm1 ^ 9) := by
    rw [hC3, hf, hd1, hd0, hdm1]; ring
  rw [hfac] at hprinc
  have hne : (X ^ 555 * (X + 1) ^ 6 : ℚ[X]) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero 555 Polynomial.X_ne_zero
    · apply pow_ne_zero 6
      rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
      exact Polynomial.X_add_C_ne_zero 1
  exact (mul_eq_zero.mp hprinc).resolve_left hne

/-- Degree bound for a tilde coefficient (kernel): from d = y^m * d̃ and deg d ≤ B,
    deg d̃ ≤ B - m. (Used to get deg d̃1 ≤ 8, deg d̃0 ≤ 12 from the paper's cota
    deg d1 ≤ 34, deg d0 ≤ 51.) -/
theorem e10_dt_bound {m B : ℕ} {d dt : ℚ[X]} (hd : d = X ^ m * dt) (hB : d.natDegree ≤ B) :
    dt.natDegree ≤ B - m := by
  by_cases hdt : dt = 0
  · simp [hdt]
  · have h1 : d.natDegree = m + dt.natDegree := by
      rw [hd, Polynomial.natDegree_mul (pow_ne_zero m Polynomial.X_ne_zero) hdt,
        Polynomial.natDegree_pow, Polynomial.natDegree_X]
      omega
    omega

/-- E10 endgame (kernel over ℚ[y]): from the nueva ecuacion principal, d̃_{-1} = (y+1)^k,
    the degree bounds deg d̃1 ≤ 8, deg d̃0 ≤ 12, and g of degree 4 with g(-1) ≠ 0,
    derive False, splitting on k ≥ 8 (divisibility) vs k ≤ 7 (degrees). -/
theorem e10_endgame (dt1 dt0 dtm1 g : ℚ[X]) (k : ℕ)
    (hnueva : 18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 8 * (X + 1) ^ 66 * g ^ 3
      + 27 * dt0 * dtm1 ^ 9 = 0)
    (hdtm1 : dtm1 = (X + 1) ^ k)
    (hdt1 : dt1.natDegree ≤ 8) (hdt0 : dt0.natDegree ≤ 12)
    (hg_deg : g.natDegree = 4) (hg_ne0 : g ≠ 0)
    (hg_neg1 : eval (-1) g ≠ 0) : False := by
  have hX1ne : (X + 1 : ℚ[X]) ≠ 0 := by
    rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
    exact Polynomial.X_add_C_ne_zero 1
  have hX1deg : (X + 1 : ℚ[X]).natDegree = 1 := by
    rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
    exact Polynomial.natDegree_X_add_C 1
  have h8ne : (8 : ℚ[X]) ≠ 0 := by
    rw [← C_ofNat]; exact C_ne_zero.mpr (by norm_num)
  have h80 : (8 : ℚ[X]).natDegree = 0 := by
    rw [← C_ofNat]; exact Polynomial.natDegree_C 8
  have h180 : (18 : ℚ[X]).natDegree = 0 := by
    rw [← C_ofNat]; exact Polynomial.natDegree_C 18
  have h270 : (27 : ℚ[X]).natDegree = 0 := by
    rw [← C_ofNat]; exact Polynomial.natDegree_C 27
  have hteq : (8 * (X + 1) ^ 66 * g ^ 3 : ℚ[X])
      = -(18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 27 * dt0 * dtm1 ^ 9) := by
    linear_combination hnueva
  rcases lt_or_ge k 8 with hk | hk
  · -- k ≤ 7: degree argument. deg term2 = 78, deg (term1 + term3) ≤ 76.
    have ht2 : (8 * (X + 1) ^ 66 * g ^ 3 : ℚ[X]).natDegree = 78 := by
      have h1 : ((8 : ℚ[X]) * (X + 1) ^ 66).natDegree = 66 := by
        rw [Polynomial.natDegree_mul h8ne (pow_ne_zero 66 hX1ne),
          Polynomial.natDegree_pow, hX1deg, h80]
      rw [Polynomial.natDegree_mul (mul_ne_zero h8ne (pow_ne_zero 66 hX1ne))
          (pow_ne_zero 3 hg_ne0), h1, Polynomial.natDegree_pow, hg_deg]
    have hk7 : ((X + 1) ^ k : ℚ[X]).natDegree ≤ 7 := by
      have h' := Polynomial.natDegree_pow_le (p := (X + 1 : ℚ[X])) (n := k)
      rw [hX1deg] at h'
      calc ((X + 1) ^ k : ℚ[X]).natDegree ≤ k * 1 := h'
        _ = k := Nat.mul_one k
        _ ≤ 7 := by omega
    have ht1 : (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g : ℚ[X]).natDegree ≤ 76 := by
      rw [hdtm1]
      have b1 : ((18 : ℚ[X]) * (X + 1) ^ 22).natDegree ≤ 22 := by
        have h := Polynomial.natDegree_mul_le (p := (18 : ℚ[X])) (q := ((X + 1) ^ 22))
        have h22 : (((X + 1) ^ 22 : ℚ[X])).natDegree = 22 := by
          rw [Polynomial.natDegree_pow, hX1deg]
        rw [h180, h22] at h
        exact h
      have b2 : ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1).natDegree ≤ 30 := by
        have h := Polynomial.natDegree_mul_le (p := ((18 : ℚ[X]) * (X + 1) ^ 22)) (q := dt1)
        exact le_trans h (Nat.add_le_add b1 hdt1)
      have b3 : ((((X + 1) ^ k) ^ 6 : ℚ[X])).natDegree ≤ 42 := by
        have h := Polynomial.natDegree_pow_le (p := ((X + 1) ^ k : ℚ[X])) (n := 6)
        calc ((((X + 1) ^ k) ^ 6 : ℚ[X])).natDegree ≤ 6 * ((X + 1) ^ k).natDegree := h
          _ ≤ 6 * 7 := Nat.mul_le_mul (le_refl 6) hk7
          _ = 42 := rfl
      have b4 : ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1 * ((X + 1) ^ k) ^ 6).natDegree ≤ 72 := by
        have h := Polynomial.natDegree_mul_le (p := ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1))
          (q := (((X + 1) ^ k) ^ 6))
        exact le_trans h (Nat.add_le_add b2 b3)
      have h := Polynomial.natDegree_mul_le
        (p := ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1 * ((X + 1) ^ k) ^ 6)) (q := g)
      rw [hg_deg] at h
      exact le_trans h (Nat.add_le_add b4 (le_refl 4))
    have ht3 : (27 * dt0 * dtm1 ^ 9 : ℚ[X]).natDegree ≤ 75 := by
      rw [hdtm1]
      have b1 : ((27 : ℚ[X]) * dt0).natDegree ≤ 12 := by
        have h := Polynomial.natDegree_mul_le (p := (27 : ℚ[X])) (q := dt0)
        rw [h270] at h
        exact le_trans h (Nat.add_le_add (le_refl 0) hdt0)
      have b2 : ((((X + 1) ^ k) ^ 9 : ℚ[X])).natDegree ≤ 63 := by
        have h := Polynomial.natDegree_pow_le (p := ((X + 1) ^ k : ℚ[X])) (n := 9)
        calc ((((X + 1) ^ k) ^ 9 : ℚ[X])).natDegree ≤ 9 * ((X + 1) ^ k).natDegree := h
          _ ≤ 9 * 7 := Nat.mul_le_mul (le_refl 9) hk7
          _ = 63 := rfl
      have h := Polynomial.natDegree_mul_le (p := ((27 : ℚ[X]) * dt0))
        (q := (((X + 1) ^ k) ^ 9))
      exact le_trans h (Nat.add_le_add b1 b2)
    have hsum : (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 27 * dt0 * dtm1 ^ 9 :
        ℚ[X]).natDegree ≤ 76 := by
      have h := Polynomial.natDegree_add_le
        (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g) (27 * dt0 * dtm1 ^ 9)
      omega
    rw [hteq, Polynomial.natDegree_neg] at ht2
    rw [ht2] at hsum
    omega
  · -- k ≥ 8: divisibility argument. (y+1)^70 divides terms 1 and 3, hence term 2;
    -- cancelling (y+1)^66 gives (y+1) | g, contradicting g(-1) ≠ 0.
    have hprime : Prime (X + 1 : ℚ[X]) := by
      have h := Polynomial.prime_X_sub_C (-1 : ℚ)
      have heq : (X - C (-1 : ℚ) : ℚ[X]) = X + 1 := by simp
      rwa [heq] at h
    have hdvd1 : ((X + 1) ^ 70 : ℚ[X]) ∣ 18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g := by
      rw [hdtm1]
      have e : ((X + 1) ^ (22 + 6 * k) : ℚ[X]) = (X + 1) ^ 22 * (X + 1) ^ (k * 6) := by
        rw [← pow_add]; congr 1; ring
      have hfac : (18 : ℚ[X]) * (X + 1) ^ 22 * dt1 * ((X + 1) ^ k) ^ 6 * g
          = (X + 1) ^ (22 + 6 * k) * (18 * dt1 * g) := by
        rw [← pow_mul, e]; ring
      rw [hfac]
      exact Dvd.dvd.mul_right (pow_dvd_pow (X + 1) (by omega : 70 ≤ 22 + 6 * k)) _
    have hdvd3 : ((X + 1) ^ 70 : ℚ[X]) ∣ 27 * dt0 * dtm1 ^ 9 := by
      rw [hdtm1]
      have e : ((X + 1) ^ (9 * k) : ℚ[X]) = ((X + 1) ^ k) ^ 9 := by
        rw [← pow_mul]; congr 1; ring
      have hfac : (27 : ℚ[X]) * dt0 * ((X + 1) ^ k) ^ 9
          = (X + 1) ^ (9 * k) * (27 * dt0) := by
        rw [← e]; ring
      rw [hfac]
      exact Dvd.dvd.mul_right (pow_dvd_pow (X + 1) (by omega : 70 ≤ 9 * k)) _
    have hdvd2 : ((X + 1) ^ 70 : ℚ[X]) ∣ 8 * (X + 1) ^ 66 * g ^ 3 := by
      rw [hteq]
      exact dvd_neg.mpr (dvd_add hdvd1 hdvd3)
    have h66 : ((X + 1) ^ 66 : ℚ[X]) ≠ 0 := pow_ne_zero 66 hX1ne
    have hdvd4 : ((X + 1) ^ 4 : ℚ[X]) ∣ 8 * g ^ 3 := by
      have e70 : ((X + 1) ^ 70 : ℚ[X]) = (X + 1) ^ 66 * (X + 1) ^ 4 := by rw [← pow_add]
      have h2 : (8 * (X + 1) ^ 66 * g ^ 3 : ℚ[X]) = (X + 1) ^ 66 * (8 * g ^ 3) := by ring
      rw [e70] at hdvd2
      rw [h2] at hdvd2
      exact (mul_dvd_mul_iff_left h66).mp hdvd2
    have hdvd_g3 : ((X + 1) : ℚ[X]) ∣ g ^ 3 := by
      have h14 : ((X + 1) ^ 1 : ℚ[X]) ∣ (X + 1) ^ 4 :=
        pow_dvd_pow (X + 1) (by norm_num)
      rw [pow_one] at h14
      have h1 : ((X + 1) : ℚ[X]) ∣ 8 * g ^ 3 := dvd_trans h14 hdvd4
      rcases hprime.dvd_or_dvd h1 with h8 | hg3
      · exfalso
        have hle := Polynomial.natDegree_le_of_dvd h8 h8ne
        rw [hX1deg, h80] at hle
        omega
      · exact hg3
    have hdvd_g : ((X + 1) : ℚ[X]) ∣ g := hprime.dvd_of_dvd_pow hdvd_g3
    have hroot : (X - C (-1 : ℚ)) ∣ g := by
      have heq : (X - C (-1 : ℚ) : ℚ[X]) = X + 1 := by simp
      rw [heq]; exact hdvd_g
    rw [Polynomial.dvd_iff_isRoot] at hroot
    exact hg_neg1 hroot

/-- E10 Theorem 5.1, CONDITIONAL assembly. `S5Counterexample` is the (opaque)
    existence of a Thm-5.1-shaped counterexample (a (9,24)/(9,27) pair with
    [P,Q] = x + g(y) and the stated Newton data). The link hypothesis packages
    the §5 data a counterexample yields — C3, f, the d's, the tilde d's, g, k —
    including the cleared principal equation and the divisibility/degree bounds;
    its proof is the open part (link_924/link_927, §5 rescaling inputs,
    coefficient-system derivation, 9-equation derivation, [GGV1] Props 1.13/2.1).
    The g-facts are kernel E13 results, transported by cancelling y(y+1). -/
theorem thm51_conditional (S5Counterexample : Prop)
    (link : S5Counterexample →
      ∃ (C3 f d1 d0 dm1 dt1 dt0 dtm1 g : ℚ[X]) (k : ℕ),
        C3 = X ^ 8 * (X + 1) ∧ f = e13f ∧ f = X * (X + 1) * g ∧
        (18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
          + 27 * C3 ^ 6 * d0 * dm1 ^ 9 = 0) ∧
        d1 = X ^ 26 * dt1 ∧ d0 = X ^ 39 * dt0 ∧ dm1 = X ^ 52 * dtm1 ∧
        dt1.natDegree ≤ 8 ∧ dt0.natDegree ≤ 12 ∧ dtm1 = (X + 1) ^ k)
    : ¬ S5Counterexample := by
  intro h
  obtain ⟨C3, f, d1, d0, dm1, dt1, dt0, dtm1, g, k, hC3, hf13, hf, hprinc, hd1, hd0, hdm1,
    hdt1, hdt0, hdtm1⟩ := link h
  have hg_eq : g = e13g := by
    have hXne : (X * (X + 1) : ℚ[X]) ≠ 0 :=
      mul_ne_zero Polynomial.X_ne_zero (by
        rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
        exact Polynomial.X_add_C_ne_zero 1)
    have h : X * (X + 1) * g = X * (X + 1) * e13g := by
      rw [← hf, hf13, e13_f_factor]
    exact mul_left_cancel₀ hXne h
  have hg_deg : g.natDegree = 4 := by rw [hg_eq]; exact e13_g_natDegree
  have hg_ne0 : g ≠ 0 := by
    rw [hg_eq]
    intro hg0
    exact e13_g_ne_zero_at_zero (by rw [hg0]; simp)
  have hg_neg1 : eval (-1) g ≠ 0 := by rw [hg_eq]; exact e13_g_ne_zero_at_neg_one
  have hnueva := e10_rescaling C3 f d1 d0 dm1 dt1 dt0 dtm1 g hC3 hf hd1 hd0 hdm1 hprinc
  exact e10_endgame dt1 dt0 dtm1 g k hnueva hdtm1 hdt1 hdt0 hg_deg hg_ne0 hg_neg1

/-! ## §9. E17 — Corollary 5.2 (CONDITIONAL assembly).

  From Thm 5.1 (as `h51`) and the link hypothesis `link52` — the ψ sixth-power
  step (Cor 7.2 + Thm 2.6 + Def 4.3 of [GGV1]) together with the φ-shift
  (φ(x) = x + λ, φ(y) = y), the bracket [φ(P),φ(Q)] = x + λ, and the sucesores
  bounds (sucesores) — which turn a Cor-5.2-shaped counterexample into a
  Thm-5.1-shaped counterexample. All of those are carried inside `link52`;
  the assembly itself is the two-line application below. -/

theorem cor52_conditional (C52Counterexample S5Counterexample : Prop)
    (h51 : ¬ S5Counterexample)
    (link52 : C52Counterexample → S5Counterexample) :
    ¬ C52Counterexample := by
  intro h
  exact h51 (link52 h)
/-!
## Assembly section — fields 9–10 of `MinimalPremises` refined by Legs B/C

### What this section does

Leg A carried fields 9–10 (`link_924`, `link_927`) as single opaque
implications: a row counterexample yields the §5 endgame data
`∃ h78, h78 = 78 ∧ h78 ≤ 76`. Legs B and C have now landed, so each opaque
link is REPLACED by a named chain of finer premises plus kernel theorems:

- `prem42` / `prem41`: the §4 reduction applies to *this* counterexample,
  i.e. the counterexample supplies a `Prop42Premises` / `Prop41Premises`
  structure (Leg B). The structure's own fields name the §4 premises:
  for (9,24): Prop 3.12 soundness (`pred_sound`), [vdE] 10.2.6
  (`pred_ne_25`), Prop 3.12(2) (`h312_2`), hybrid-vs-slip
  (`hybrid_slip : HybridSlip924`); for (9,27): the Cor 7.4 / φ₃ / Prop 8.2
  data fields of `Prop41Premises`.
- `prop42_conditional` / `prop41_conditional` (Leg B, KERNEL, copied above):
  from those structures, the reduced Newton polygons are exactly the
  Theorem 5.1 shapes. `prop42_shape_of` / `prop41_shape_of` extract the
  pure shapes (`Prop42Shape` / `Prop41Shape`) from the conditional
  conclusions.
- `bridge924` / `bridge927`: the polynomial-level lift — a Thm-5.1-shaped
  vertex list comes from actual `P, Q` with `[P,Q] = x + g(y)` (and, for
  (9,27), the Cor 5.7 Succ/ψ step turning a Prop-4.1 polygon into a
  Cor-5.2-shaped counterexample). CARRIED, NOT proved by any leg: Leg B is
  vertex-list level only ("the polynomial-level statement is NOT claimed:
  it needs the Laurent layer (R14/INTERFACE)"), and Leg C's `cor52`
  carries the ψ sixth-power step (Cor 7.2 / Thm 2.6 / Def 4.3) inside its
  own link. The bridge is the precise remaining gap between the §4
  vertex-level reduction and the §5 polynomial-level input.
- `link51_924` / `link51_927`: the §5 link hypothesis of Leg C's
  `thm51_conditional` — a Thm-5.1-shaped counterexample yields the §5 data
  (C₃, f, the d's, the principal equation, the degree bounds). CARRIED:
  the §5 rescaling inputs, the coefficient-system derivation, the
  9-equation derivation, and [GGV1] Props 1.13/2.1 are the open part
  (Leg C header, E10).
- `link52_927`: the Cor 5.2 link of Leg C's `cor52_conditional` — a
  Cor-5.2-shaped counterexample yields a Thm-5.1-shaped one. CARRIED
  (Cor 7.2 / Thm 2.6 / Def 4.3 / ψ sixth-power step).
- `thm51_conditional` (Leg C, KERNEL [triple], copied above) + the kernel
  §5 endgame close the chain: from the §5 data, `False`.

`link_924_derived` / `link_927_derived` prove Leg A's opaque links from
the refined premises, by kernel composition. `theorem21_minimal_v2` is
Leg A's `theorem21_minimal` with fields 9–10 replaced by the refined
chain. Fields 1–8 and 11 are UNCHANGED from Leg A (red rows; §3-84 link;
Prop 3.29; §3-120 link; enumeration completeness).

### Honest status

Fields 9–10 are REFINED, not unconditionally discharged. What Legs B/C
discharged: the §4 vertex-level reductions (kernel, given their premise
structures) and the §5 endgame (kernel, given the §5 data link). What
remains carried, now with precise names: the bridge (polynomial lift +
Cor 5.7 step), the §5 data link, the Cor 5.2 link, and the §4 premise
structures' own fields (HybridSlip924, Prop 3.12, [vdE] 10.2.6,
Prop 3.12(2)). No `theorem21_unconditional` is claimed.

Prop 4.4 (`prop44_conditional`, Leg B) is copied into this file as part
of Leg B's content, but it is NOT on the minimal premise list for
Theorem 2.1: the (7,21) row is eliminated via §3 (`discard_721_via_sec3`),
so the §6 route (Leg D's `s6_theorem61`, CONDITIONAL) is a second proof
of the same elimination, not a premise of this assembly.
-/

/-- The pure (9,24) reduced shape: one of Prop 4.2's three final polygons,
    with Jacobian-factor pair `(-1, 1)`. Extracted from
    `prop42_conditional` (the `preP924_*` map equalities are dropped). -/
def Prop42Shape : Prop :=
  ∃ finalP finalQ : List Pt,
    ((finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)] ∧
      finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)]) ∨
     ((finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)] ∧
       finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)]) ∨
      (finalP = [(0, 0), (1, 1), (6, 16), (6, 18)] ∧
       finalQ = [(0, 0), (1, 0), (9, 24), (9, 27)]))) ∧
    phiJacPair 3 = (-1, 1)

/-- The pure (9,27) reduced shape: Prop 4.1's final polygon, with
    Jacobian-factor pair `(-1, 1)`. Extracted from `prop41_conditional`. -/
def Prop41Shape : Prop :=
  ∃ finalP finalQ : List Pt,
    finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)] ∧
    finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)] ∧
    phiJacPair 3 = (-1, 1)

/-- `prop42_conditional`'s conclusion, stripped to the pure shape. -/
theorem prop42_shape_of {H : Prop} (h : Prop42Premises H) : Prop42Shape := by
  obtain ⟨P, Q, hdisj, hjac⟩ := prop42_conditional h
  refine ⟨P, Q, ?_, hjac⟩
  rcases hdisj with ⟨_, _, hP, hQ⟩ | ⟨_, _, hcases⟩
  · exact Or.inl ⟨hP, hQ⟩
  · exact Or.inr hcases

/-- `prop41_conditional`'s conclusion, stripped to the pure shape. -/
theorem prop41_shape_of (h : Prop41Premises) : Prop41Shape := by
  obtain ⟨P, Q, _, _, hP, hQ, hjac⟩ := prop41_conditional h
  exact ⟨P, Q, hP, hQ, hjac⟩

/-- The §5 data link type of Leg C's `thm51_conditional`, as a named
    definition so the two `MinimalPremises2` link fields share one text.
    `S` is the opaque Thm-5.1-shaped counterexample proposition. -/
def S5Link (S : Prop) : Prop :=
  S →
    ∃ (C3 f d1 d0 dm1 dt1 dt0 dtm1 g : ℚ[X]) (k : ℕ),
      C3 = X ^ 8 * (X + 1) ∧ f = e13f ∧ f = X * (X + 1) * g ∧
      (18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 = 0) ∧
      d1 = X ^ 26 * dt1 ∧ d0 = X ^ 39 * dt0 ∧ dm1 = X ^ 52 * dtm1 ∧
      dt1.natDegree ≤ 8 ∧ dt0.natDegree ≤ 12 ∧ dtm1 = (X + 1) ^ k

/-- The REFINED minimal premise list for Theorem 2.1 (20 fields).
    Fields 1–5: the five red rows (EXTERNAL, as in Leg A).
    Field 6: the §3-84 link ([GGV6] Thm 7.3 + the §3 computation).
    Field 7: [GGV2] Prop 3.29 in universal form.
    Field 8: the §3-120 last-possible-corner computation.
    Fields 9a–9e (replacing Leg A's `link_924`): the (9,24) chain —
    `HybridSlip924` (hybrid-vs-slip, published §7 NOT FOUND),
    `prem42` (the §4 reduction applies to this counterexample),
    `S5Counterexample924` (opaque Thm-5.1-shaped counterexample),
    `bridge924` (vertex-list shape → polynomial counterexample; the
    Laurent-layer lift, NOT proved),
    `link51_924` (the §5 data link; rescaling + coefficient-system +
    9-equation derivation + [GGV1] Props 1.13/2.1, OPEN).
    Fields 10a–10f (replacing Leg A's `link_927`): the (9,27) chain —
    `prem41` (the §4 reduction applies to this counterexample),
    `C52Counterexample927` (opaque Cor-5.2-shaped counterexample),
    `S5Counterexample927` (opaque Thm-5.1-shaped counterexample),
    `bridge927` (Prop-4.1 shape → Cor-5.2-shaped counterexample;
    the Cor 5.7 Succ/ψ step + the polynomial lift, NOT proved),
    `link52_927` (Cor 7.2 / Thm 2.6 / Def 4.3 / ψ sixth-power step, OPEN),
    `link51_927` (the §5 data link, as for (9,24)).
    Field 11: [GGV5] enumeration completeness (`TableCompleteness`). -/
structure MinimalPremises2 where
  red_412_34 : ¬ CounterexampleAt ⟨(4, 12), 3, 4, 64⟩
  red_412_57 : ¬ CounterexampleAt ⟨(4, 12), 5, 7, 112⟩
  red_520_23 : ¬ CounterexampleAt ⟨(5, 20), 2, 3, 75⟩
  red_520_32 : ¬ CounterexampleAt ⟨(5, 20), 3, 2, 75⟩
  red_824_23 : ¬ CounterexampleAt ⟨(8, 24), 2, 3, 96⟩
  link_84 : CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ →
    ∃ (IM Im : Int), IM ≥ Im ∧ IM = 4 ∧ Im = 5
  prop329 : ∀ (a b : Nat), LPC (a, b) → b + Nat.gcd a b ≠ a
  link_120 : CounterexampleAt ⟨(8, 32), 3, 2, 120⟩ → LPC (8, 4)
  HybridSlip924 : Prop
  prem42 : CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ → Prop42Premises HybridSlip924
  S5Counterexample924 : Prop
  bridge924 : Prop42Shape → S5Counterexample924
  link51_924 : S5Link S5Counterexample924
  prem41 : CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ → Prop41Premises
  C52Counterexample927 : Prop
  S5Counterexample927 : Prop
  bridge927 : Prop41Shape → C52Counterexample927
  link52_927 : C52Counterexample927 → S5Counterexample927
  link51_927 : S5Link S5Counterexample927
  enum_complete : ∀ (degP degQ : Nat), Counterexample degP degQ →
    max degP degQ < 125 →
    ∃ r ∈ table, CounterexampleAt r ∧ degreePair r = (degP, degQ)

/-- Leg A's `link_924`, derived from the refined (9,24) chain:
    counterexample → `Prop42Premises` → `Prop42Shape` (kernel, Leg B) →
    Thm-5.1-shaped counterexample (bridge, carried) → §5 data (link,
    carried) → `False` (kernel, Leg C `thm51_conditional`) → the endgame
    data, ex falso. -/
theorem link_924_derived (h : MinimalPremises2 CounterexampleAt Counterexample LPC) :
    CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ →
      ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76 := by
  intro hc
  have h42 := h.prem42 hc
  have hshape := prop42_shape_of h42
  have hc5 := h.bridge924 hshape
  have hnot := thm51_conditional h.S5Counterexample924 h.link51_924
  exact (hnot hc5).elim

/-- Leg A's `link_927`, derived from the refined (9,27) chain:
    counterexample → `Prop41Premises` → `Prop41Shape` (kernel, Leg B) →
    Cor-5.2-shaped counterexample (bridge, carried) → Thm-5.1-shaped
    counterexample (`link52_927`, carried) → §5 data (link, carried) →
    `False` (kernel, Leg C `thm51_conditional` via `cor52_conditional`)
    → the endgame data, ex falso. -/
theorem link_927_derived (h : MinimalPremises2 CounterexampleAt Counterexample LPC) :
    CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ →
      ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76 := by
  intro hc
  have h41 := h.prem41 hc
  have hshape := prop41_shape_of h41
  have hc52 := h.bridge927 hshape
  have h51 := thm51_conditional h.S5Counterexample927 h.link51_927
  have hnot52 := cor52_conditional h.C52Counterexample927 h.S5Counterexample927
    h51 h.link52_927
  exact (hnot52 hc52).elim

/-- Theorem 2.1, from the refined minimal premises: if (P,Q) is a
    counterexample with max degree < 125, then
    (deg P, deg Q) ∈ {(72,108), (108,72)}. Fields 9–10 are the Leg B/C
    refined chains (above); fields 1–8 and 11 are Leg A's, unchanged.
    NO unconditional Theorem 2.1 is claimed: the refined fields are still
    carried premises, now with their internal structure named. -/
theorem theorem21_minimal_v2
    (h : MinimalPremises2 CounterexampleAt Counterexample LPC)
    (degP degQ : Nat) (hce : Counterexample degP degQ) (hmax : max degP degQ < 125) :
    (degP, degQ) = (72, 108) ∨ (degP, degQ) = (108, 72) := by
  obtain ⟨r, hr, hcr, hpair⟩ := h.enum_complete degP degQ hce hmax
  rcases table_cases r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hcr h.red_412_34
  · exact absurd hcr h.red_412_57
  · exact absurd hcr h.red_520_23
  · exact absurd hcr h.red_520_32
  · exact absurd hcr (discard_84_row CounterexampleAt h.link_84)
  · exact absurd hcr h.red_824_23
  · right
    exact hpair.symm
  · exact absurd hcr (discard_120_row CounterexampleAt LPC h.prop329 h.link_120)
  · exact absurd hcr (discard_924_row CounterexampleAt
      (link_924_derived CounterexampleAt Counterexample LPC h))
  · exact absurd hcr (discard_927_row CounterexampleAt
      (link_927_derived CounterexampleAt Counterexample LPC h))

/-- Theorem 2.1 in conditional form (same statement, premises packaged). -/
theorem theorem21_conditional_minimal_v2
    (h : MinimalPremises2 CounterexampleAt Counterexample LPC)
    (degP degQ : Nat) (hce : Counterexample degP degQ) (hmax : max degP degQ < 125) :
    (degP, degQ) = (72, 108) ∨ (degP, degQ) = (108, 72) :=
  theorem21_minimal_v2 CounterexampleAt Counterexample LPC h degP degQ hce hmax

/-! ### Discharge audit (assembly stage — for the inventory)

| Leg A field | Status after assembly | Carried now (named) |
|---|---|---|
| 1–5 red rows | CARRIED, unchanged | [GGV4] §3.5, [M], [H], [GGV3] §5, [GGV5] Prop 6.1 (Leg F R20, CONDITIONAL) |
| 6 link_84 | CARRIED, unchanged | [GGV6] Thm 7.3 + π-root machinery (Leg F: NOT PROVED as a theorem) |
| 7 prop329 | CARRIED, unchanged | [GGV2] Prop 3.29 (Leg F: CONDITIONAL on FinitasData premises) |
| 8 link_120 | CARRIED, unchanged | last-possible-corner computation + Thm 7.6(5) numbering (Leg F: CONDITIONAL) |
| 9 link_924 | REFINED (not unconditionally discharged) | `prem42` (§4 structure: HybridSlip924, Prop 3.12, [vdE] 10.2.6, Prop 3.12(2)); `bridge924` (polynomial lift, Laurent layer); `link51_924` (§5 data link) |
| 10 link_927 | REFINED (not unconditionally discharged) | `prem41` (§4 structure); `bridge927` (Cor 5.7 Succ/ψ step + polynomial lift); `link52_927` (Cor 7.2 / Thm 2.6 / Def 4.3 / ψ); `link51_927` (§5 data link) |
| 11 enum_complete | CARRIED, unchanged | [GGV5] enumeration completeness (Leg F: BLOCKED) |

Kernel steps composed in this file: `prop41_conditional` [propext,
Quot.sound], `prop42_conditional` [triple], `thm51_conditional` [triple],
`cor52_conditional` [no axioms] (all re-verified by the assembly run
below). The §6 route for the (7,21) row is NOT on the minimal list
(`discard_721_via_sec3`); `prop44_conditional` is present in this file
but consumes no assembly premise.
-/

#print axioms prop41_conditional
#print axioms prop42_conditional
#print axioms prop43_conditional
#print axioms prop44_conditional
#print axioms thm51_conditional
#print axioms cor52_conditional
#print axioms prop42_shape_of
#print axioms prop41_shape_of
#print axioms link_924_derived
#print axioms link_927_derived
#print axioms theorem21_minimal_v2
