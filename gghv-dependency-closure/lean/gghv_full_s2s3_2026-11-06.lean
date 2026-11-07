import Mathlib

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
