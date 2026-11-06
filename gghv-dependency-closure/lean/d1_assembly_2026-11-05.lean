import Mathlib

/-!
# AssemblyPremises leg — [GGV1] Theorem 2.1, discharge map (scratch)

**CLAIM:** Each of Part5's 7 `AssemblyPremises` fields is discharged as far as the
proved machinery allows: the internal arithmetic/structure is proved
unconditionally (KERNEL), and each field's remaining content is isolated as ONE
explicitly named hypothesis (a "link") whose mathematical justification is
documented. The final theorem `theorem21_minimal` proves Theorem 2.1's degree-pair
disjunction from a MINIMAL, explicitly enumerated premise list (11 fields).
**STATUS:** PROVED (conditional on the minimal list) — see the round log.

## Per-field status (Part5_Assembly.lean, 149 lines)

- `red_rows_discarded` — CARRIED as 5 separate hypotheses (one per red row,
  each named with its citation). These are EXTERNAL: the cited papers' theorems,
  not formalized here. Per-row citations verified from the GGHV TeX (lines
  308–313): (4,12)/(3,4) via [GGV4] §3.5, [M], [H]; (4,12)/(5,7) via
  [GGV4] §3.5; (5,20)/(2,3) and (5,20)/(3,2) via [GGV3] §5; (8,24)/(2,3)
  via [GGV5] Prop. 6.1. Note (TeX line 295): [M] considered max ∈ {64,75,84,99}
  but only case 64 has a complete proof — so the (5,20) discards rest on
  [GGV3] §5, not on [M].
- `discard_84` — CONDITIONAL THEOREM PROVED (`discard_84_row`): the §3-84
  numerics are KERNEL (I_M = 4, I_m = 5, Part2/Part25 restated), and the
  discard follows from ONE link hypothesis `link_84` (a row-84 counterexample's
  intersection numbers satisfy I_M ≥ I_m with values 4, 5). Justification of
  the link: [GGV6] Thm. 7.3 (the inequality) + GGHV §3's F₉-family computation
  (the values). The remaining gap is exactly: formalize [GGV6]'s π-root
  machinery and apply Thm. 7.3 to the F₉ family.
- `discard_120` — CONDITIONAL THEOREM PROVED (`discard_120_row`): the §3-120
  data are KERNEL (en_{4,-1}(F_1) = (6,21), gcd(2,7) = 1, corner (8,4));
  the Prop. 3.29 exclusion is KERNEL arithmetic (4 + gcd(8,4) = 8); the discard
  follows from the general [GGV2] Prop. 3.29 (carried, as a universal statement
  over the abstract last-possible-corner predicate `LPC`) + ONE link hypothesis
  `link_120` (a row-120 counterexample would make (8,4) the last possible corner
  of φ(P)). Remaining gap: the last-possible-corner computation (Directions
  library) + [GGV2] Prop. 3.29 itself. (TeX: the 120 argument is "mentioned in
  [GGV2] Remark 3.31" (line 299) and the discard itself is "by [GGV2]
  Proposition 3.29" (line 388) — both citations are in the TeX; Part1's header
  names Remark 3.31, Part2's names Prop. 3.29.)
- `discard_924` — CONDITIONAL THEOREM PROVED (`discard_924_row`): the §5
  endgame is KERNEL (`thm5_endgame`: a degree-78 term cannot equal terms bounded
  by 75/76); the discard follows from ONE link hypothesis `link_924` (a row-924
  counterexample's §4 reduction + §5 elimination yield the principal equation
  with those bounds). Justification of the link: Prop. 4.2 reduction (INTERFACE,
  needs Laurent algebra + Cor. 7.4 + Prop. 8.2) + the §5 elimination (SymPy I1:
  resultant = −27/(64·d_{−1}³) × the paper's principal equation, remainder 0;
  logs `elimination_s5.log` — a single-route CAS check, NOT a Lean proof) +
  the C-expansion bounds (INTERFACE, needs the Laurent-series library).
- `discard_927` — CONDITIONAL THEOREM PROVED (`discard_927_row`): same §5
  endgame, via ONE link hypothesis `link_927` (Prop. 4.1 reduction instead of
  4.2; Cor. 5.7's Succ/ψ step is part of the link's justification). The §5
  theorem (TeX 1402) covers BOTH the (9,24) and the (9,27) shapes in one
  statement — the two rows share the §5 elimination; they differ in the §4
  reduction.
- `discard_721` — DISCHARGED VIA §3, NOT VIA §6. **Key finding: the (7,21)
  row IS the max=84 row** (table row 5: ⟨(7,21), 2, 3, 84⟩). So `discard_84`
  and `discard_721` are two discard arguments for the SAME row, and the §3
  route (`discard_721_via_sec3`, identical to `discard_84_row`) already
  eliminates it. The §6 route (principal equation, k = 2 derivation, non-square
  contradiction, Prop. 4.4 reduction) is therefore NOT on the minimal premise
  list for Theorem 2.1 — it is the paper's second proof of the same elimination
  (TeX line 321: "In section 5 we offer another proof for this case" — and §6
  likewise). `discard_721` AS PART5 LITERALLY DEFINES IT (via §6) is NOT
  discharged: only the degree check at k = 2 is KERNEL (`thm6_principal_degrees_at_k2`);
  the §6 elimination certificate, the k = 2 derivation, the final non-square
  contradiction, the Prop. 4.4 reduction, and the Prop. 4.4/§6 polygon-link open
  check (Part3: prop44 vs thm721 lists differ — (6,2)/(9,3) vs (2,6)/(3,9))
  are all still open. They are recorded in the §6 section, not claimed.
- `enumeration` — CARRIED as ONE hypothesis `enum_complete` ([GGV5] §§5–6
  completeness: every counterexample with max < 125 has its shape among the 10
  table rows). The table-side checks are KERNEL (all 10 max degrees < 125;
  exactly 5 red rows; remaining max degrees [84, 108, 120, 99, 108]; source
  count 7 + 3 = 10; (5,20) occurs in exactly two rows; (72,108) arises from
  two rows). The completeness proof itself is open (Parts 28–32 are definitions
  + checks only).

## The minimal premise list (MinimalPremises, 11 fields)

1–5. The five red-row discards (EXTERNAL, one per row, citations above).
6. `link_84` — [GGV6] Thm. 7.3 + §3 computation (discharges BOTH discard_84
   AND discard_721, same row).
7. `prop329` — [GGV2] Prop. 3.29, universal form over `LPC`.
8. `link_120` — the §3-120 last-possible-corner computation.
9. `link_924` — Prop. 4.2 + §5 elimination (SymPy I1) + bounds.
10. `link_927` — Prop. 4.1 + §5 elimination (SymPy I1) + bounds + Cor. 5.7 step.
11. `enum_complete` — [GGV5] enumeration completeness.

Minimality: every field is used by `theorem21_minimal`; no two fields are the
same claim; the §6 items are excluded because route A (field 6) already
eliminates the (7,21) row. What is NOT claimed: `theorem21_unconditional` —
Theorem 2.1 stays CONDITIONAL on these 11 premises (which is exactly the
content of the 7 Part5 fields, with the (7,21) redundancy removed and the
red-row field split into its five cited theorems).

## Qualifications carried (unchanged)

- Pairwise bracket form inherited from the extremos file (D2 combine step still
  open); central is conditional (Joseph 2.2 + Lema Joseph carried); Cor. 7.4 is
  conditional (mayores' T-termination + D2 power laws carried); hybrid-vs-slip
  still open (published Cor. 7.4 text missing). The §4 reductions used in
  fields 9–10 depend on Cor. 7.4 + Prop. 8.2, hence inherit those conditions.
- The abstract predicates: `CounterexampleAt : CaseRow → Prop` (a counterexample
  with the given Newton shape), `Counterexample : Nat → Nat → Prop` (a
  counterexample with the given degree pair), `LPC : Nat × Nat → Prop`
  ([GGV2] Def. 3.21, last possible corner). They are parameters of this file;
  no claim is made about their definitions.
- The paper's disjunction is proved via the (108,72) member: the proof shows the
  given counterexample's pair is (108,72) (the (8,28) row as oriented). The
  (72,108) member is the SAME row with P and Q exchanged
  (`swapPair (108,72) = (72,108)`, proved by `rfl` in `theorem21_degree_pairs`);
  the exchange is the Keller-condition symmetry [Q,P] = −[P,Q], not a separate
  row — so no extra premise is needed for it, and none is claimed.
-/

/-! ### Section 1 — The §2 table (Part1/Part5 content, restated) -/

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

/- The abstract predicates this file is parameterized by (see the header):
    `CounterexampleAt` (a counterexample with the given Newton shape),
    `Counterexample` (a counterexample with the given degree pair),
    `LPC` ([GGV2] Def. 3.21, last possible corner). -/
variable (CounterexampleAt : CaseRow → Prop) (Counterexample : Nat → Nat → Prop)
  (LPC : Nat × Nat → Prop)

/-- The remaining degree pairs, given the premises:
    (108,72) from the (8,28) row, and (72,108) by swap. -/
theorem theorem21_degree_pairs :
    [degreePair row828, swapPair (degreePair row828)] =
      [(108, 72), (72, 108)] := by
  rfl

/-- Ten-way case split on a table row. -/
theorem table_cases (r : CaseRow) (h : r ∈ table) :
    r = ⟨(4, 12), 3, 4, 64⟩ ∨ r = ⟨(4, 12), 5, 7, 112⟩ ∨
    r = ⟨(5, 20), 2, 3, 75⟩ ∨ r = ⟨(5, 20), 3, 2, 75⟩ ∨
    r = ⟨(7, 21), 2, 3, 84⟩ ∨ r = ⟨(8, 24), 2, 3, 96⟩ ∨
    r = ⟨(8, 28), 3, 2, 108⟩ ∨ r = ⟨(8, 32), 3, 2, 120⟩ ∨
    r = ⟨(9, 24), 2, 3, 99⟩ ∨ r = ⟨(9, 27), 2, 3, 108⟩ := by
  simp only [table, List.mem_cons, List.mem_nil_iff, or_false] at h
  exact h

/-! ### Section 2 — The red rows (Part1/Part28 content, restated) -/

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

/-- Rows remaining after the red discards, as degree pairs: the five
    non-red rows are (7,21), (8,28), (8,32), (9,24), (9,27). -/
theorem remaining_after_red :
    (table.filter (fun r => r ∉ redRows)).map degreePair =
      [(56, 84), (108, 72), (120, 80), (66, 99), (72, 108)] := by
  rfl

/-- Rows surviving the paper's §2/§3 discards: remove the five red rows and the
    max = 84 and max = 120 rows. The survivors are exactly the (8,28), (9,24)
    and (9,27) rows. -/
theorem section2_survivors :
    ((table.filter (fun r => r.maxDeg ≠ 84 ∧ r.maxDeg ≠ 120)).map degreePair).filter
      (fun p => p ≠ (48, 64) ∧ p ≠ (80, 112) ∧ p ≠ (50, 75) ∧ p ≠ (75, 50) ∧
        p ≠ (64, 96)) = [(108, 72), (66, 99), (72, 108)] := by
  rfl

/-! ### Section 3 — The §3-84 discard, and (7,21) via §3 (Part2/Part25 content, restated) -/

/-- §3, max = 84 case: family F₉ data. A₀ = (7,21), A₁ = (11/7, 2), k = 1,
    m = j + 2, n = 2j + 3. -/
def f9_m (j : Nat) : Nat := j + 2

theorem f9_m_at_j0 : f9_m 0 = 2 := by rfl

/-- The paper's I_M sum at j = 0, before cancelling 7:
    7 major roots × (2m) with m = 2 gives 28. -/
theorem im_84_sum_at_j0 : 7 * (2 * f9_m 0) = 28 := by decide

/-- Cancelling the 7: 28 / 7 = 4, so I_M = 4 at j = 0. -/
theorem im_84_at_j0 : 28 / 7 = 4 := by rfl

/-- The paper's I_m formula, in Int arithmetic: one final minor π-root with
    δ = -3 gives δ + 1 = -2; the 7 minor roots contribute 7 * (-2/7) = -2.
    Hence I_m = 1 - (-2) - (-2) = 5. -/
theorem im_minor_84 :
    (1 : Int) - (-2) - (7 * (-2) / 7) = 5 := by decide

/-- The numeric contradiction at the heart of the §3-84 discard: I_M = 4 and
    I_m = 5, so I_M < I_m. -/
theorem discard_84_numeric : (4 : Int) < 5 := by decide

/-- I_M = I(P,Q) and I_m ≤ I(P,Q) combine to I_m ≤ I_M (GGHV's Thm. 7.3),
    as a carried bundle: the two theorems are [GGV6]'s; only the combination
    is proved here (Part25's `im_le_IM`, restated). -/
structure IntersectionFormulas where
  IM : Int
  Im : Int
  IPQ : Int
  hM : IM = IPQ
  hm : Im ≤ IPQ

theorem im_le_IM (F : IntersectionFormulas) : F.Im ≤ F.IM := by
  rw [F.hM]
  exact F.hm

/-- The §3-84 discard, in Part2's conditional form: it takes [GGV6] Thm. 7.3
    (I_M ≥ I_m) and the computed values as hypotheses, so no false arithmetic
    statement is ever axiomatized. -/
theorem discard_84_conditional (IM IMm : Int) (h73 : IM ≥ IMm)
    (hIM : IM = 4) (hIm : IMm = 5) : False := by
  rw [hIM, hIm] at h73
  exact absurd h73 (by decide : ¬ (4 : Int) ≥ 5)

/-- The §3-84 discard, as a row elimination. The link hypothesis `h84` is the
    precise remaining premise: a counterexample at the (7,21) row has
    intersection numbers satisfying I_M ≥ I_m with values 4 and 5. Its
    justification is [GGV6] Thm. 7.3 (the inequality) + GGHV §3's F₉-family
    computation (the values, proved above). The remaining gap is exactly:
    formalize [GGV6]'s π-root machinery and apply Thm. 7.3 to the F₉ family. -/
theorem discard_84_row
    (h84 : CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ →
      ∃ (IM Im : Int), IM ≥ Im ∧ IM = 4 ∧ Im = 5) :
    ¬ CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ := by
  intro hc
  obtain ⟨IM, Im, hge, h4, h5⟩ := h84 hc
  exact discard_84_conditional IM Im hge h4 h5

/-- The (7,21) row via §6 is the SAME row: ⟨(7,21), 2, 3, 84⟩ is both the
    max=84 row and the §6 row. So the §3 route already eliminates it, and the
    §6 route is not needed for Theorem 2.1. This is the same theorem as
    `discard_84_row`, under its other Part5 field name. -/
theorem discard_721_via_sec3
    (h84 : CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ →
      ∃ (IM Im : Int), IM ≥ Im ∧ IM = 4 ∧ Im = 5) :
    ¬ CounterexampleAt ⟨(7, 21), 2, 3, 84⟩ :=
  discard_84_row CounterexampleAt h84

/-! ### Section 4 — The §3-120 discard (Part2/Part21/Part22 content, restated) -/

/-- §3, max = 120 case: the data the paper computes.
    A₀ = (8,32), A₁ = (8,28), A₂ = (11/4, 7), direction (ρ₁, σ₁) = (4, -1). -/
def corner_120_a0 : Nat × Nat := (8, 32)
def corner_120_a1 : Nat × Nat := (8, 28)

/-- en_{4,-1}(F_1) = (6,21), and (6,21) = (3/4) * (8,28) as rational points:
    6 * 4 = 3 * 8 and 21 * 4 = 3 * 28. -/
theorem discard_120_data :
    (6 * 4 = 3 * 8 ∧ 21 * 4 = 3 * 28) := by
  decide

/-- q_1 = 4, from [GGV1] Thm. 7.6(5): q_1 = 4 | d_0 with d_0 ≤ 4, and
    st_{1,0}(P) = (8,28) = 4 * (2,7) with gcd(2,7) = 1. -/
theorem discard_120_gcd : Nat.gcd 2 7 = 1 := by rfl

/-- The transformed corner after φ(x) = x, φ(y) = y + λ_1: A₀' = (8,4). -/
def corner_120_transformed : Nat × Nat := (8, 4)

theorem corner_120_transformed_eq : corner_120_transformed = (8, 4) := by
  rfl

/-- [GGV2] Prop. 3.29 ("casos imposibles"), applied to (8,4): a last possible
    corner (a,b) must satisfy b + gcd(a,b) ≠ a; but 4 + gcd(8,4) = 8 = a.
    This arithmetic is KERNEL; the proposition itself is carried as the
    hypothesis `h329` below. -/
theorem prop329_exclusion_84 : 4 + Nat.gcd 8 4 = 8 := by decide

/-- The §3-120 discard, as a row elimination. Two carried items: the general
    [GGV2] Prop. 3.29 (as a universal statement over the abstract `LPC`
    predicate — this shape is faithful and non-circular, since it quantifies
    over all (a,b), not over the specific row) and the link hypothesis `h120`
    (a row-120 counterexample would make (8,4) the last possible corner of
    φ(P)). Remaining gaps: the last-possible-corner computation (Directions
    library) + [GGV2] Prop. 3.29 itself. -/
theorem discard_120_row
    (h329 : ∀ (a b : Nat), LPC (a, b) → b + Nat.gcd a b ≠ a)
    (h120 : CounterexampleAt ⟨(8, 32), 3, 2, 120⟩ → LPC (8, 4)) :
    ¬ CounterexampleAt ⟨(8, 32), 3, 2, 120⟩ := by
  intro hc
  exact h329 8 4 (h120 hc) prop329_exclusion_84

/-- The §3-120 discard, in argument-shape form only (Part2's version): P is the
    abstract proposition "the (8,32) case occurs and φ(P) has (8,4) as its last
    possible corner". -/
theorem discard_120_argument_shape (P : Prop) (h_would : P) (h_cannot : ¬ P) :
    False :=
  h_cannot h_would

/-! ### Section 5 — The §5 discards: (9,24) and (9,27) (Part4 content, restated) -/

/-- §5 Theorem ("teorema impossible", TeX 1402) conditions, as data:
    [P,Q] = x + g(y); en_{3,-1}(P) = st_{1,0}(P) = (6,16);
    st_{-1,1}(P) = en_{1,0}(P) = (6,18);
    en_{3,-1}(Q) = st_{1,0}(Q) = (9,24);
    st_{-1,1}(Q) = en_{1,0}(Q) = (9,27).
    Note: ONE theorem covers both the (9,24) and the (9,27) shapes. -/
def thm5_en_P : Nat × Nat := (6, 16)
def thm5_en_Q : Nat × Nat := (9, 24)
def thm5_st_P : Nat × Nat := (6, 18)
def thm5_st_Q : Nat × Nat := (9, 27)

/-- §5 degree bounds from the paper's endgame, kernel-checked:
    12 + 9*7 = 75 and 22 + 8 + 42 + 4 = 76. -/
theorem thm5_bounds : (12 + 9 * 7 = 75 ∧ 22 + 8 + 42 + 4 = 76) := by
  decide

/-- §5: deg((y+1)^66 g(y)^3) = 78 forces deg g = 4, since 66 + 3 * deg g = 78. -/
theorem thm5_g_degree : 66 + 3 * 4 = 78 := by rfl

/-- §5 endgame, conditionally: if the principal equation equates a degree-78
    term with terms bounded by 75 and 76, that is impossible. Stated with the
    bounds as hypotheses so the conditionality is explicit. -/
theorem thm5_endgame (h78 : Nat) (h_bound : h78 ≤ 76) (h_eq : h78 = 78) :
    False := by
  rw [h_eq] at h_bound
  exact absurd h_bound (by decide : ¬ (78 : Nat) ≤ 76)

/-- The (9,24) discard, as a row elimination. The link hypothesis `h924` is the
    precise remaining premise: a counterexample at the (9,24) row, after the
    Prop. 4.2 reduction and the §5 elimination, yields the principal equation
    equating a degree-78 term with terms bounded by 76. Its justification is
    Prop. 4.2 (INTERFACE: needs the Laurent algebra + Cor. 7.4 + Prop. 8.2) +
    the §5 elimination (SymPy I1: resultant = −27/(64·d_{−1}³) × the paper's
    principal equation, remainder 0; `elimination_s5.log` — a single-route CAS
    check, NOT a Lean proof) + the C-expansion bounds (INTERFACE: needs the
    Laurent-series library). -/
theorem discard_924_row
    (h924 : CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ →
      ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76) :
    ¬ CounterexampleAt ⟨(9, 24), 2, 3, 99⟩ := by
  intro hc
  obtain ⟨h78, heq, hle⟩ := h924 hc
  exact thm5_endgame h78 hle heq

/-- The (9,27) discard, as a row elimination. Same §5 endgame; the link
    hypothesis `h927` differs from `h924` in the §4 reduction (Prop. 4.1
    instead of Prop. 4.2) and in that Cor. 5.7's Succ/ψ step is part of its
    justification (the step from Thm. 5.1 to the (9,27) row's elimination,
    INTERFACE: needs the (m,n)-pair machinery of [GGV1] Def. 4.3 / Cor. 7.2). -/
theorem discard_927_row
    (h927 : CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ →
      ∃ (h78 : Nat), h78 = 78 ∧ h78 ≤ 76) :
    ¬ CounterexampleAt ⟨(9, 27), 2, 3, 108⟩ := by
  intro hc
  obtain ⟨h78, heq, hle⟩ := h927 hc
  exact thm5_endgame h78 hle heq

/-! ### Section 6 — The (7,21) row via §6: what is proved, what is NOT -/

/-- §6 Theorem ("teorema impossible para 7", TeX 1817) conditions, as data:
    [P,Q] = x; N(P) = {(0,0),(4,0),(2,6),(0,14)};
    N(Q) = {(0,0),(6,0),(3,9),(0,21)}. -/
def thm6_P : List (Nat × Nat) := [(0, 0), (4, 0), (2, 6), (0, 14)]
def thm6_Q : List (Nat × Nat) := [(0, 0), (6, 0), (3, 9), (0, 21)]

/-- §6 principal equation degrees: with d_{-1} = α y^k, deg d_0 = 9,
    deg d_1 = 6, the three terms have degrees 15 + 6k, 27, 9 + 9k.
    At k = 2 all three are 27. This degree check is KERNEL. -/
theorem thm6_principal_degrees_at_k2 :
    (15 + 6 * 2 = 27 ∧ 9 + 9 * 2 = 27) := by
  decide

/-- §6 scaling check: (4,0)->(6,0), (2,6)->(3,9), (0,14)->(0,21), all
    factor 3/2 by cross-multiplication (Part3's `thm721_scaling`, restated). -/
theorem thm721_scaling :
    (6 * 2 = 4 * 3 ∧ 3 * 2 = 2 * 3 ∧ 9 * 2 = 6 * 3 ∧ 0 * 2 = 0 * 3) := by
  decide

/-- The §6 route is NOT claimed here. What remains open for it, itemized:
    (i) the §6 elimination to the principal equation (SymPy I1 only,
    `elimination_s6.log`: resultant = −27/(64·d_{−1}³) × the paper's principal
    equation, remainder 0 — the Lean elimination certificate is still open);
    (ii) the derivation of k = 2 (INTERFACE); (iii) the final non-square
    contradiction, (27α⁹d₀ − 2y⁹)²/(108α¹⁰) = α³y⁸ − 2λy¹⁰ with a non-square
    right side (INTERFACE: needs polynomial square / degree-in-y arguments);
    (iv) the Prop. 4.4 reduction (INTERFACE: needs the Laurent algebra +
    Cor. 7.4 + Prop. 8.2 + [GGV2] Prop. 3.12 + [GGV6] Prop. 2.5);
    (v) the Prop. 4.4/§6 polygon-link open check (Part3: the (6,2)/(9,3)
    vertices of Prop. 4.4 appear as (2,6)/(3,9) in §6 — the exact
    transformation linking the two lists is NOT asserted anywhere).
    None of (i)–(v) is needed for Theorem 2.1, because the §3 route
    (`discard_721_via_sec3`) already eliminates the row. -/
theorem sec6_route_not_needed : True := by
  trivial

/-! ### Section 7 — The enumeration table (Parts 28/31/32 content, restated) -/

/-- The (72,108) pair from the (9,27) row, directly. -/
theorem pair_72_108_from_927 : (2 * (9 + 27), 3 * (9 + 27)) = (72, 108) := by
  decide

/-- The (72,108) pair from the (8,28) row, swapped. This is why eliminating
    the (9,27) ROW does not eliminate the degree PAIR (72,108) — Part5's
    row-vs-degree-pair correction, now computed. -/
theorem pair_72_108_from_828_swapped : (2 * (8 + 28), 3 * (8 + 28)) = (72, 108) := by
  decide

/-- The (5,20) A₀ occurs in exactly two rows of the table (with (m,n) = (2,3)
    and (3,2)) — GGHV's note that the max-75 case "corresponds to two cases in
    two different families" — so the §5 contribution is 7 rows, and 7 + 3 = 10
    rows total, matching the table. -/
def rowsA0 : List (Nat × Nat × Nat × Nat) :=
  [ (4, 12, 3, 4), (4, 12, 5, 7), (5, 20, 2, 3), (5, 20, 3, 2)
  , (7, 21, 2, 3), (8, 24, 2, 3), (8, 28, 3, 2), (8, 32, 3, 2)
  , (9, 24, 2, 3), (9, 27, 2, 3) ]

theorem rowsA0_length : rowsA0.length = 10 := by decide

theorem rowsA0_520_twice :
    (rowsA0.filter (fun r => r.1 = 5 && r.2.1 = 20)).length = 2 := by
  decide

theorem source_count : 7 + 3 = 10 := by decide

/-- Max degree from the family formula: max(m,n)·(a+b). The computed max degree
    equals the table's in all 10 rows. -/
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

/-! ### Section 8 — The assembly: minimal premises + Theorem 2.1 -/

/-- The MINIMAL remaining premise list for Theorem 2.1 (11 fields).
    Every field is used by `theorem21_minimal`; no two fields are the same
    claim; the §6 items are excluded because field 6 already eliminates the
    (7,21) row. Fields 1–5 are the five cited theorems for the red rows
    (EXTERNAL). Field 6 packages [GGV6] Thm. 7.3 + the §3 computation. Field 7
    is [GGV2] Prop. 3.29 in universal form. Field 8 is the §3-120
    last-possible-corner computation. Fields 9–10 package the §4 reductions +
    the §5 elimination (SymPy I1) + the bounds (+ Cor. 5.7's step for field 10).
    Field 11 is [GGV5] enumeration completeness. -/
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

/-- Theorem 2.1, from the minimal premises: if (P,Q) is a counterexample with
    max degree < 125, then (deg P, deg Q) ∈ {(72,108), (108,72)}.
    Proof: the enumeration gives a table row r for the counterexample; the
    ten-way case split eliminates every row except (8,28) (red rows by fields
    1–5; (7,21) by field 6 via `discard_84_row`; (8,32) by fields 7–8 via
    `discard_120_row`; (9,24)/(9,27) by fields 9–10 via the §5 endgame); the
    survivor row gives degreePair (108,72). The (72,108) disjunct is the same
    row with P and Q exchanged (see the file header). -/
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

/-- Theorem 2.1 in Part5's shape: the same statement, with the premises
    packaged as the structure. This is `theorem21_conditional` with the 7
    opaque `AssemblyPremises` fields replaced by the 11 minimal premises above
    (the (7,21) redundancy removed, the red-row field split into its five cited
    theorems). Theorem 2.1 stays CONDITIONAL on these 11 premises — no
    `theorem21_unconditional` is claimed. -/
theorem theorem21_conditional_minimal (h : MinimalPremises CounterexampleAt Counterexample LPC)
    (degP degQ : Nat) (hce : Counterexample degP degQ) (hmax : max degP degQ < 125) :
    (degP, degQ) = (72, 108) ∨ (degP, degQ) = (108, 72) :=
  theorem21_minimal CounterexampleAt Counterexample LPC h degP degQ hce hmax

/-! ### Discharge map (summary, for the parent's report)

| Part5 field | Status in this file | Remaining premise(s) |
|---|---|---|
| red_rows_discarded | CARRIED (5 hyps, fields 1–5) | [GGV4] §3.5; [GGV4] §3.5; [GGV3] §5; [GGV3] §5; [GGV5] Prop. 6.1 |
| discard_84 | CONDITIONAL THEOREM (`discard_84_row`) | field 6: [GGV6] Thm. 7.3 + §3 computation |
| discard_120 | CONDITIONAL THEOREM (`discard_120_row`) | fields 7–8: [GGV2] Prop. 3.29 + LPC computation |
| discard_924 | CONDITIONAL THEOREM (`discard_924_row`) | field 9: Prop. 4.2 + §5 elim (SymPy I1) + bounds |
| discard_927 | CONDITIONAL THEOREM (`discard_927_row`) | field 10: Prop. 4.1 + §5 elim (SymPy I1) + bounds + Cor. 5.7 |
| discard_721 | DISCHARGED VIA §3 (`discard_721_via_sec3`) | same as discard_84 (field 6); §6 route NOT needed, NOT claimed |
| enumeration | CARRIED (field 11) | [GGV5] §§5–6 completeness |

Final: `theorem21_minimal` proves Theorem 2.1 from the 11-field minimal list.
No `theorem21_unconditional`. The §6 route, the D2 combine step, central's
Joseph 2.2 / Lema Joseph, mayores' T-termination, and hybrid-vs-slip remain
open as documented in the header and in the earlier legs' files.
-/
