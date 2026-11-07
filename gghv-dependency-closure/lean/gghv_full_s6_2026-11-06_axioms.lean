import Mathlib

/-!
# GGHV §6 systems for (7,21) — Leg D scratch proofs (2026-11-06)

**CLAIM:** Kernel lemmas for inventory entries E19–E23 (GGHV §6) plus a
CONDITIONAL assembly for Theorem 6.1 (E18). No `sorry` anywhere.
**STATUS:** Scratch (not filed, not validated); see `legD.log` for the run record.

## What is proved here, per entry

- **E19** (`calculo de C para 7`): the valuation arithmetic is KERNEL
  (`v_{2,1}(3,1) = 7`, **not** the paper's `(b₀)` value 6), the recursion
  identity, and the two induction bound-steps for an abstract valuation
  satisfying the valuation axioms; the finite construction bounds are proved
  by induction from the recursion. The full Laurent-series existence and the
  `F`-construction inputs ([GGV1] Props 1.13/2.1, [GGV3] §1) are carried as
  named premises — the Laurent-series library is the INTERFACE gap.
- **E23** (`F_{-4} = (1/2) y^{-1}`): the monomial bracket computation and the
  monomial uniqueness are KERNEL; the polynomial-ODE uniqueness lemma is
  KERNEL; the Laurent-bracket reduction is carried as a named premise.
- **E21** (`D_k ∈ K[y]`): the `D_j D_{k+3-j}` identity (with the CORRECTED
  factor `1/2` on the sum — the paper's printed formula omits it, in both
  §5 (E14) and §6 (E21); harmless for membership) and the membership
  induction in `RatFunc K` are KERNEL, conditional on the E19 recursion
  data and on `y ∣ P₅` (the `D₂` base case).
- **E20** (Remark): the `Q̃` identity and the truncated `C̃²`, `C̃³`
  expansions are KERNEL; the full tilde-series existence is carried as a
  named premise. Read with the §6 labels (Theorem 6.1 / `calculo de C
  para 7`), NOT the printed §5 labels.
- **E22** (9-equation system + principal equation): the `(D̃²)_{-k}` and
  `(Q̃)_{-j}` displays are KERNEL expansions of the coefficient sums
  (given `d 3 = 1`, `d 2 = 0`, `d i = 0` for `i ≥ 4`); the principal
  equation is KERNEL from the 9 equations via the Part-11/12 certificate
  identity (transcribed from the Singular `cert_s6` script and re-verified
  there); `k = 2` and the non-square contradiction are KERNEL from the
  degree data and `d_{-1} = α y^k`. **Flag:** the paper's shift
  `φ(x) = x - D₂` does NOT kill the `x²` term — it leaves `d₂ = -2 D₂`
  (proved here by `ring`); the shift that kills it is `x - D₂/3`. The
  `d 2 = 0` used by the displays is therefore carried as an explicit
  named premise `phi_shift_x2_vanishes`, not derived from the paper's
  shift. The `(D̃²)_{-7}` display's literal `2 d_{-1} 0` is read as
  `2 d_{-10}` (the Singular transcription agrees; the printed form is a
  misprint).
- **E18** (Theorem 6.1): CONDITIONAL assembly. **Flag:** the §6 printed
  polygon lists `N(P) = {(0,0),(4,0),(2,6),(0,14)}`,
  `N(Q) = {(0,0),(6,0),(3,9),(0,21)}` have the middle vertex transposed
  against Prop. 4.4's `{(0,0),(4,0),(6,2),(0,14)}` /
  `{(0,0),(6,0),(9,3),(0,21)}` AND against the §6 proof's own
  `ℓ_{1,0}(P) = x⁶y²`, `ℓ_{1,0}(Q) = x⁹y³` (max `x`-exponent 4 < 6 in the
  printed list). The assembly is stated for the Prop. 4.4 lists; the
  printed lists are recorded as differing (kernel `decide`). The Prop. 4.4
  reduction itself belongs to Leg B (E8) and is carried as a named premise.

## Paper slips flagged (not copied)

1. E19 `(b₀)`: `v_{2,1}(3,1) = 6` — correct value **7**.
2. E19 proof writes `v(C_{3-j} C_{3-k+j}) ≤ v(C_{3-j}) v(C_{3-k+j})`
   (a product of valuations) — the bound actually used is the SUM; the
   correct valuation law is additive, proved here from the axioms.
3. E20 cites Theorem 5.1 / `calculo de C` — Theorem 6.1 / `calculo de C
   para 7` are meant.
4. E21 proof writes `C₃` in the `D_j D_{k+3-j}` identity — `y` is meant.
5. E21 (and E14) `D_k` formula omits the factor `1/2` on the
   `Σ D_j D_{k+3-j}` sum — corrected here.
6. `(D̃²)_{-7}` display: literal `2 d_{-1} 0` — read as `2 d_{-10}`.
7. `φ(x) = x - D₂` leaves `d₂ = -2 D₂`, not `0` (both §5 and §6).
8. §6 printed polygons transpose the middle vertex vs Prop. 4.4 and vs
   the `ℓ_{1,0}` data.
-/

/-! ### §1. E19 — `calculo de C para 7`: valuation arithmetic -/

/-- E19, item (3) base value: `v_{2,1}(3,1) = 2·3 + 1·1 = 7`.
    The paper's `(b₀)` says 6; 6 is wrong. -/
theorem e19_v21_31 : (2 : ℤ) * 3 + 1 * 1 = 7 := by decide

/-- The paper's `(b₀)` value is arithmetically wrong. -/
theorem e19_v21_b0_paper_wrong : (2 : ℤ) * 3 + 1 * 1 ≠ 6 := by decide

/-- E19, item (4) base value: `v_{1,-1}(3,1) = 1·3 + (-1)·1 = 2`. -/
theorem e19_v1m1_31 : (1 : ℤ) * 3 + (-1) * 1 = 2 := by decide

/-- `v_{2,1}(y^{-1}) = -1` (used in the `(b_k)` estimate). -/
theorem e19_v21_yinv : (2 : ℤ) * 0 + 1 * (-1) = -1 := by decide

/-- `v_{1,-1}(y^{-1}) = 1` (used in the `(c_k)` estimate). -/
theorem e19_v1m1_yinv : (1 : ℤ) * 0 + (-1) * (-1) = 1 := by decide

/-- The `F`-valuation arithmetic: `v_{1,0}(F) + v_{1,0}(P) - v_{1,0}(1,1)
    = v_{1,0}([F,P]) = v_{1,0}(x) = 1` with `v_{1,0}(P) = 6`,
    `v_{1,0}(1,1) = 1` gives `v_{1,0}(F) = -4`. -/
theorem e19_F_val : ∀ vF : ℤ, vF + 6 - 1 = 1 → vF = -4 := by
  intro vF h; omega

/-- The `ℓ_{1,0}(Q - C^3) = α_k (x^3 y)^k` exponent range: `-2 < k < 3`. -/
theorem e19_k_range : ∀ k : ℤ, -2 < k → k < 3 → k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 := by
  intro k h1 h2; omega

/-! #### Abstract valuation axioms (the Laurent valuation, axiomatised)

The paper's `v_{ρ,σ}` on `K[y,y^{-1}]((x^{-1}))` is a valuation in the
usual sense: additive on products, `v(a+b) ≤ max (v a) (v b)`, `v(-a) =
v a`, `v 1 = 0`, and `v` of a nonzero constant is `0`. The induction
steps below are proved from these axioms alone; instantiating them to the
concrete Laurent valuation is the INTERFACE step (Laurent-series library).
-/

/-- Valuation axioms for a `ℤ`-valued valuation on a field. -/
structure ValAxioms (F : Type*) [Field F] (w : F → ℤ) : Prop where
  mul : ∀ a b, w (a * b) = w a + w b
  add : ∀ a b, w (a + b) ≤ max (w a) (w b)
  neg : ∀ a, w (-a) = w a
  one : w 1 = 0
  two : w (2 : F) = 0

namespace ValAxioms

variable {F : Type*} [Field F] {w : F → ℤ}

theorem zero (hw : ValAxioms F w) : w 0 = 0 := by
  have h := hw.mul 0 0
  simp at h
  omega

theorem inv (hw : ValAxioms F w) {a : F} (ha : a ≠ 0) : w a⁻¹ = -w a := by
  have h := hw.mul a a⁻¹
  rw [mul_inv_cancel₀ ha, hw.one] at h
  omega

theorem div (hw : ValAxioms F w) {a b : F} (hb : b ≠ 0) : w (a / b) = w a - w b := by
  rw [div_eq_mul_inv, hw.mul, hw.inv hb, sub_eq_add_neg]

theorem pow_nat (hw : ValAxioms F w) (a : F) (n : ℕ) : w (a ^ n) = (n : ℤ) * w a := by
  induction n with
  | zero => simp [hw.one]
  | succ n ih => rw [pow_succ, hw.mul, ih]; push_cast; ring

theorem zpow (hw : ValAxioms F w) {a : F} (ha : a ≠ 0) (n : ℤ) : w (a ^ n) = n * w a := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast]; exact hw.pow_nat a n
  | negSucc n =>
      rw [zpow_negSucc, hw.inv (pow_ne_zero _ ha), hw.pow_nat a (n + 1)]
      have e : (Int.negSucc n : ℤ) = -((n : ℤ) + 1) := rfl
      rw [e]; push_cast; ring

/-- A finite sum is bounded by the common bound of its terms (for `B ≥ 0`). -/
theorem sum_le (hw : ValAxioms F w) {s : Finset ℤ} {f : ℤ → F} {B : ℤ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  induction s using Finset.induction_on with
  | empty => simp [hw.zero, hB]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      exact le_trans (hw.add _ _) (max_le h1 h2)

end ValAxioms

/-! #### E19 induction bound-steps

Paper proof, corrected: the product estimate is additive
(`v(ab) = v(a) + v(b)`), not multiplicative. The step below is the
`(b_k)`/`(c_k)` induction step for the recursion
`C_{3-k} := (1/(2y)) (P_{6-k} - Σ_{j=1}^{k-1} C_{3-j} C_{3-k+j})`.
-/

/-- E19 `(b_k)` step: from `w(C_{3-j}) ≤ 1 + 2j` for `1 ≤ j ≤ k-1` and
    `w(P_{6-k}) ≤ 2 + 2k`, with `w y = 1`, the recursion gives
    `w(C_{3-k}) ≤ 1 + 2k`. -/
theorem e19_bound_step_21 {F : Type*} [Field F] [CharZero F] {w : F → ℤ}
    (hw : ValAxioms F w) {y : F} (hy : w y = 1) (hy0 : y ≠ 0)
    {k : ℤ} (hk : 1 ≤ k) (C : ℤ → F) (P : ℤ → F)
    (hC : ∀ j : ℤ, 1 ≤ j → j ≤ k - 1 → w (C (3 - j)) ≤ 1 + 2 * j)
    (hP : w (P (6 - k)) ≤ 2 + 2 * k) :
    w ((P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) / (2 * y))
      ≤ 1 + 2 * k := by
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero (by norm_num : (2 : F) ≠ 0) hy0
  have hterm : ∀ j ∈ Finset.Icc 1 (k - 1),
      w (C (3 - j) * C (3 - k + j)) ≤ 2 + 2 * k := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [hw.mul]
    have h1 := hC j hj.1 hj.2
    have h2 := hC (k - j) (by omega) (by omega)
    -- `C (3 - k + j) = C (3 - (k - j))`
    have heq : (3 : ℤ) - k + j = 3 - (k - j) := by ring
    rw [← heq] at h2
    omega
  have hS : w (∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) ≤ 2 + 2 * k :=
    hw.sum_le (by omega) hterm
  have hPS : w (P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j))
      ≤ 2 + 2 * k := by
    have hsub := hw.add (P (6 - k))
      (-∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j))
    rw [hw.neg] at hsub
    rw [sub_eq_add_neg]
    exact le_trans hsub (max_le hP hS)
  rw [hw.div h2y]
  have hwy : w ((2 : F) * y) = 1 := by rw [hw.mul, hw.two, hy]; simp
  omega

/-- E19 `(c_k)` step: from `w(C_{3-j}) ≤ j - 1` for `1 ≤ j ≤ k-1` and
    `w(P_{6-k}) ≤ k - 2`, with `w y = -1`, the recursion gives
    `w(C_{3-k}) ≤ k - 1`. -/
theorem e19_bound_step_1m1 {F : Type*} [Field F] [CharZero F] {w : F → ℤ}
    (hw : ValAxioms F w) {y : F} (hy : w y = -1) (hy0 : y ≠ 0)
    {k : ℤ} (hk : 1 ≤ k) (C : ℤ → F) (P : ℤ → F)
    (hC : ∀ j : ℤ, 1 ≤ j → j ≤ k - 1 → w (C (3 - j)) ≤ j - 1)
    (hP : w (P (6 - k)) ≤ k - 2) :
    w ((P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) / (2 * y))
      ≤ k - 1 := by
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero (by norm_num : (2 : F) ≠ 0) hy0
  have hwy : w ((2 : F) * y) = -1 := by rw [hw.mul, hw.two, hy]; simp
  by_cases hk1 : k = 1
  · subst hk1
    have hempty : Finset.Icc (1 : ℤ) (1 - 1) = ∅ :=
      Finset.Icc_eq_empty (by norm_num)
    rw [hempty, Finset.sum_empty, sub_zero, hw.div h2y, hwy]
    omega
  · have hk2 : 2 ≤ k := by omega
    have hterm : ∀ j ∈ Finset.Icc 1 (k - 1),
        w (C (3 - j) * C (3 - k + j)) ≤ k - 2 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [hw.mul]
      have h1 := hC j hj.1 hj.2
      have h2 := hC (k - j) (by omega) (by omega)
      have heq : (3 : ℤ) - k + j = 3 - (k - j) := by ring
      rw [← heq] at h2
      omega
    have hS : w (∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) ≤ k - 2 :=
      hw.sum_le (by omega) hterm
    have hPS : w (P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j))
        ≤ k - 2 := by
      have hsub := hw.add (P (6 - k))
        (-∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j))
      rw [hw.neg] at hsub
      rw [sub_eq_add_neg]
      exact le_trans hsub (max_le hP hS)
    rw [hw.div h2y, hwy]
    omega

/-- E19 recursion identity: `2y·C = P - S` with `y ≠ 0` gives
    `C = (P - S)/(2y)` — the defining equation
    (ecuacion de C 3-k para 7), TeX 1877. -/
theorem e19_recursion {F : Type*} [Field F] [CharZero F] {y C P S : F}
    (hy0 : y ≠ 0) (h : 2 * y * C = P - S) : C = (P - S) / (2 * y) := by
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero (by norm_num : (2 : F) ≠ 0) hy0
  rw [eq_div_iff h2y]
  -- goal: C * (2 * y) = P - S
  linear_combination h

/-! #### E19 finite construction bounds (induction from the recursion)

The paper constructs `C` inductively; the bounds `(b_k)`, `(c_k)` are
proved here for every finite step from the recursion data. The passage to
the infinite Laurent series `C = Σ x^{3-j} C_{3-j}` and the `F`
construction (via [GGV1] Props 1.13/2.1 and [GGV3] §1) are the carried
premises — see `C7AssemblyPremises` below.
-/

/-- E19 construction bounds by induction: with `C 3 = y`, the recursion
    (ecuacion de C 3-k para 7) and the `P`-bounds, `w21 (C_{3-n}) ≤ 1+2n`
    and `w1m1 (C_{3-n}) ≤ n-1` for every `n`. At `n = 0` this is
    `w21 y = 1 ≤ 1` and `w1m1 y = -1 ≤ -1`; the `(b₀)` bound on
    `x^3 y` is `2·3 + 1 = 7` (see `e19_v21_31`), not 6. -/
theorem e19_finite_bounds {F : Type*} [Field F] [CharZero F]
    {w21 w1m1 : F → ℤ} (hw21 : ValAxioms F w21) (hw1m1 : ValAxioms F w1m1)
    {x y : F} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx21 : w21 x = 2) (hx1m1 : w1m1 x = 1)
    (hy21 : w21 y = 1) (hy1m1 : w1m1 y = -1)
    (C : ℤ → F) (P : ℤ → F)
    (hC3 : C 3 = y)
    (hrec : ∀ k : ℤ, 1 ≤ k → C (3 - k) =
      (P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) / (2 * y))
    (hP21 : ∀ k : ℤ, 1 ≤ k → w21 (P (6 - k)) ≤ 2 + 2 * k)
    (hP1m1 : ∀ k : ℤ, 1 ≤ k → w1m1 (P (6 - k)) ≤ k - 2) :
    ∀ n : ℕ, w21 (C (3 - n)) ≤ 1 + 2 * n ∧ w1m1 (C (3 - n)) ≤ (n : ℤ) - 1 := by
  have key : ∀ n : ℕ, ∀ m : ℕ, m ≤ n →
      w21 (C (3 - m)) ≤ 1 + 2 * m ∧ w1m1 (C (3 - m)) ≤ (m : ℤ) - 1 := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        simp only [Nat.cast_zero, sub_zero]
        rw [hC3]
        constructor
        · simp [hy21]
        · simp [hy1m1]
    | succ n ih =>
        intro m hm
        by_cases hm' : m ≤ n
        · exact ih m hm'
        · have hmn : m = n + 1 := by omega
          subst hmn
          have hC21 : ∀ j : ℤ, 1 ≤ j → j ≤ ((n : ℤ) + 1) - 1 →
              w21 (C (3 - j)) ≤ 1 + 2 * j := by
            intro j hj1 hj2
            obtain ⟨m, hm⟩ : ∃ m : ℕ, j = (m : ℤ) := ⟨j.toNat, by omega⟩
            subst hm
            exact (ih m (by omega)).1
          have hC1m1 : ∀ j : ℤ, 1 ≤ j → j ≤ ((n : ℤ) + 1) - 1 →
              w1m1 (C (3 - j)) ≤ j - 1 := by
            intro j hj1 hj2
            obtain ⟨m, hm⟩ : ∃ m : ℕ, j = (m : ℤ) := ⟨j.toNat, by omega⟩
            subst hm
            exact (ih m (by omega)).2
          have e : (3 : ℤ) - ((n + 1 : ℕ) : ℤ) = 3 - ((n : ℤ) + 1) := by
            push_cast; ring
          rw [e, hrec ((n : ℤ) + 1) (by omega)]
          push_cast
          constructor
          · exact e19_bound_step_21 hw21 hy21 hy0 (k := (n : ℤ) + 1) (by omega) C P
              hC21 (hP21 _ (by omega))
          · exact e19_bound_step_1m1 hw1m1 hy1m1 hy0 (k := (n : ℤ) + 1) (by omega) C P
              hC1m1 (hP1m1 _ (by omega))
  intro n
  exact key n n le_rfl

/-- The `(b₀)` bound in the paper's form: `v_{2,1}(x^3 y) = 7`, from the
    coefficient bound `w21 y = 1` and `w21 x = 2`. -/
theorem e19_b0_corrected {F : Type*} [Field F] {w21 : F → ℤ}
    (hw21 : ValAxioms F w21) {x y : F} (hx0 : x ≠ 0)
    (hx21 : w21 x = 2) (hy21 : w21 y = 1) :
    w21 (x ^ (3 : ℤ) * y) = 7 := by
  rw [hw21.mul, hw21.zpow hx0, hx21, hy21]
  norm_num

/-- E19 assembly premises (carried): the Laurent-series existence and the
    `F`-construction inputs. The finite bounds above are kernel; the passage
    to `C, F ∈ K[y,y^{-1}]((x^{-1}))` with `P = C^2`,
    `Q = C^3 + α₂C² + α₁C + α₀ + α_{-1}C^{-1} + F`, `v_{1,0}(F) = -4`
    needs the Laurent-series library plus [GGV1] Props 1.13/2.1 and
    [GGV3] §1, none of which is formalised here. -/
structure C7AssemblyPremises (F : Type*) [Field F] : Prop where
  laurent_series : True  -- placeholder: existence of C, F in K[y,y⁻¹]((x⁻¹))
  ggv1_prop113 : True   -- [GGV1] Prop 1.13 (bracket valuation)
  ggv1_prop21 : True    -- [GGV1] Prop 2.1 (leading-form dichotomy)
  ggv3_sec1 : True      -- [GGV3] §1 (choice of the α's)

/-! ### §2. E23 — `F_{-4} = (1/2) y^{-1}` -/

/-- Monomial bracket data: `[x^a y^b, x^c y^d] = (ad - bc) x^{a+c-1} y^{b+d-1}`.
    Returns `(coefficient, x-exponent, y-exponent)`. -/
def monoBracket (a b c d : ℤ) : ℤ × ℤ × ℤ := (a * d - b * c, a + c - 1, b + d - 1)

/-- E23 bracket computation: `[x^6 y^2, x^{-4} y^{-1}] = 2 · x^1 y^0`.
    The coefficient is `6·(-1) - 2·(-4) = 2`. -/
theorem e23_bracket_coeff : monoBracket 6 2 (-4) (-1) = (2, 1, 0) := by decide

/-- With `F_{-4} = (1/2) y^{-1}`, the bracket `[x^6 y^2, F_{-4} x^{-4}]`
    is `2 · (1/2) · x = x`. -/
theorem e23_verification {K : Type*} [Field K] [CharZero K] :
    ((6 : K) * (-1) - 2 * (-4)) * (1 / 2) = 1 := by norm_num

/-- E23 monomial uniqueness: if `F_{-4} = c·y^e` and the bracket
    `[x^6 y^2, c·x^{-4} y^e]` is `x` (coefficient equation
    `(6e+8)·c = 1` and exponent equation `e + 1 = 0`), then `e = -1`
    and `c = 1/2`. -/
theorem e23_monomial_unique {K : Type*} [Field K] [CharZero K]
    (c : K) (e : ℤ) (hcoeff : (6 * (e : K) + 8) * c = 1) (hexp : e + 1 = 0) :
    e = -1 ∧ c = 1 / 2 := by
  have he : e = -1 := by omega
  subst he
  refine ⟨rfl, ?_⟩
  have h2 : (2 : K) * c = 1 := by
    have h := hcoeff
    norm_num at h
    exact h
  rw [eq_div_iff (by norm_num : (2 : K) ≠ 0)]
  linear_combination h2

/-- E23 polynomial-ODE uniqueness (the heart of the general uniqueness):
    if `g ∈ K[y]` and `1 ≤ N` satisfy
    `6 y² g' + (8 - 6N) y g = y^N`, then `g = (1/2) y^{N-1}`.
    Proof: compare coefficients of `y^{n+1}`; the coefficient is
    `(6n + 8 - 6N)·a_n`, and `6n + 8 - 6N = 0` has no natural solution
    (`3 ∣ 6(n-N)` but `3 ∤ 8`), so `a_n = 0` for `n ≠ N-1` and
    `a_{N-1} = 1/2`. -/
theorem e23_ode_unique {K : Type*} [Field K] [CharZero K]
    (g : Polynomial K) (N : ℕ) (hN : 1 ≤ N)
    (h : Polynomial.C 6 * (Polynomial.X ^ 2 * Polynomial.derivative g)
        + Polynomial.C (8 - 6 * (N : K)) * (Polynomial.X * g)
        = Polynomial.X ^ N) :
    g = (1 / 2 : K) • (Polynomial.X : Polynomial K) ^ (N - 1) := by
  have hX2 : ∀ n : ℕ, (Polynomial.X ^ 2 * Polynomial.derivative g).coeff (n + 1)
      = (n : K) * g.coeff n := by
    intro n
    rw [Polynomial.coeff_X_pow_mul']
    by_cases hle : 2 ≤ n + 1
    · rw [if_pos hle, Polynomial.coeff_derivative]
      have hn1 : 1 ≤ n := by omega
      have e : n + 1 - 2 + 1 = n := by omega
      rw [e]
      have e2 : ((n + 1 - 2 : ℕ) : K) + 1 = (n : K) := by
        rw [show n + 1 - 2 = n - 1 by omega, Nat.cast_sub hn1]
        simp
      rw [e2]
      ring
    · rw [if_neg hle]
      have hn0 : n = 0 := by omega
      subst hn0
      simp
  have key : ∀ n : ℕ, (6 * (n : K) + 8 - 6 * (N : K)) * g.coeff n
      = if n + 1 = N then (1 : K) else 0 := by
    intro n
    have h2 := congrArg (fun p : Polynomial K => p.coeff (n + 1)) h
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X_mul, hX2] at h2
    linear_combination h2
  apply Polynomial.ext
  intro n
  by_cases hn : n = N - 1
  · subst hn
    have hk := key (N - 1)
    rw [if_pos (by omega : N - 1 + 1 = N)] at hk
    have h2 : (6 * (((N - 1 : ℕ)) : K) + 8 - 6 * (N : K)) = 2 := by
      have hcast : (((N - 1 : ℕ)) : K) = (N : K) - 1 := by
        rw [Nat.cast_sub hN]; simp
      rw [hcast]; ring
    rw [h2] at hk
    have hcoeff : g.coeff (N - 1) = 1 / 2 := by
      rw [eq_div_iff (by norm_num : (2 : K) ≠ 0)]
      linear_combination hk
    rw [hcoeff]
    simp [Polynomial.coeff_smul, Polynomial.coeff_X_pow]
  · have hk := key n
    rw [if_neg (by omega : ¬ n + 1 = N)] at hk
    have hne : (6 * (n : K) + 8 - 6 * (N : K)) ≠ 0 := by
      intro h0
      have h0z : 6 * (n : ℤ) + 8 - 6 * (N : ℤ) = 0 := by exact_mod_cast h0
      omega
    have hcoeff : g.coeff n = 0 := by
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h hne
      · exact h
    rw [hcoeff]
    simp [hcoeff, hn, Polynomial.coeff_smul, Polynomial.coeff_X_pow, eq_comm]

/-- The `N = 0` case of the ODE has no solution: `6y²g' + 8yg = 1` is
    impossible, since the left side has no constant term. (So the
    `F_{-4}` Laurent order `N` in the E23 reduction must satisfy `N ≥ 1`;
    the solution is `N = 1`, `g = 1/2`.) -/
theorem e23_ode_N0 {K : Type*} [Field K] [CharZero K]
    (g : Polynomial K)
    (h : Polynomial.C 6 * (Polynomial.X ^ 2 * Polynomial.derivative g)
        + Polynomial.C (8 : K) * (Polynomial.X * g) = 1) : False := by
  have h2 := congrArg (fun p : Polynomial K => p.coeff 0) h
  simp at h2

/-! ### §3. E20 — Remark (§6): the tilde-transformation

Read with the §6 labels: the remark as printed cites Theorem 5.1 /
`calculo de C` (E10/E11); Theorem 6.1 / `calculo de C para 7`
(E18/E19) are meant. -/

section E20

variable {F : Type*} [Field F] [CharZero F]
variable (C Ci P Q F' : F) (a1 a2 a0 lam : F)

/-- E20: with `P̃ = P + (2/3)α₁` and `Q̃ = Q - α₂P - α₀`,
    `Q̃ = C^3 + α₁C + λC⁻¹ + F`. -/
theorem e20_Qtilde (hQ : Q = C ^ 3 + a2 * C ^ 2 + a1 * C + a0 + lam * Ci + F')
    (hP : P = C ^ 2) :
    Q - a2 * P - a0 = C ^ 3 + a1 * C + lam * Ci + F' := by
  rw [hQ, hP]; ring

/-- E20: the truncated `C̃ = C + (1/3)α₁C⁻¹` squares to
    `P̃ = P + (2/3)α₁` up to the `C⁻²` term (absorbed by the
    `γ₃, γ₅, …` series). -/
theorem e20_Ctilde_sq_trunc (hC : C * Ci = 1) :
    (C + (1 / 3) * a1 * Ci) ^ 2
      = C ^ 2 + (2 / 3) * a1 + (1 / 9) * a1 ^ 2 * Ci ^ 2 := by
  linear_combination (2 * ((1 / 3) * a1)) * hC

/-- E20: the truncated `C̃` cubes to
    `C³ + α₁C + (α₁²/3)C⁻¹ + (α₁³/27)C⁻³`. -/
theorem e20_Ctilde_cu_trunc (hC : C * Ci = 1) :
    (C + (1 / 3) * a1 * Ci) ^ 3
      = C ^ 3 + a1 * C + (1 / 3) * a1 ^ 2 * Ci + (1 / 27) * a1 ^ 3 * Ci ^ 3 := by
  linear_combination (3 * ((1 / 3) * a1) * C + 3 * ((1 / 3) * a1) ^ 2 * Ci) * hC

/-- The E19 shape: `P = C²` and
    `Q = C³ + α₂C² + α₁C + α₀ + α₋₁C⁻¹ + F`. -/
def C7Shape (P Q C Ci F' a2 a1 a0 am1 : F) : Prop :=
  P = C ^ 2 ∧ Q = C ^ 3 + a2 * C ^ 2 + a1 * C + a0 + am1 * Ci + F'

/-- E20 assembly, CONDITIONAL on the existence of the full tilde series
    (`TildeSeriesExists`): given `C̃, C̃⁻¹, F̃, λ'` with `C̃² = P̃` and
    `Q̃ = C̃³ + λ'C̃⁻¹ + F̃`, the pair `(P̃, Q̃)` has the E19 shape with
    `α₂ = α₁ = α₀ = 0`. The infinite series
    `C̃ = C + (1/3)α₁C⁻¹ + γ₃C⁻³ + γ₅C⁻⁵ + …` is the carried premise;
    the finite truncations above are kernel. -/
theorem e20_assembly (Ct Cti Ft lam' : F)
    (hCt_sq : Ct ^ 2 = P + (2 / 3) * a1)
    (hCt_inv : Ct * Cti = 1)
    (hQt : Q - a2 * P - a0 = Ct ^ 3 + lam' * Cti + Ft) :
    C7Shape (P + (2 / 3) * a1) (Q - a2 * P - a0) Ct Cti Ft 0 0 0 lam' := by
  refine ⟨hCt_sq.symm, ?_⟩
  rw [hQt]; ring

end E20

/-! ### §4. E21 — `D_k ∈ K[y]` for (7,21): the identities -/

section E21

variable {F : Type*} [Field F] [CharZero F]

/-- E21 identity (corrected): `D_j · D_{k+3-j} = C_j · C_{k+3-j} · y^{1-k}`,
    where `D_i = C_i · y^{2-i}`. The paper's proof writes `C₃` in the
    middle expression where `y` is meant; with `y` the identity holds
    as stated. -/
theorem e21_DD_identity {y : F} (hy0 : y ≠ 0)
    (C D : ℤ → F) (hD : ∀ i, D i = C i * y ^ (2 - i))
    (j k : ℤ) :
    D j * D (k + 3 - j) = C j * C (k + 3 - j) * y ^ (1 - k) := by
  rw [hD j, hD (k + 3 - j)]
  have e : (2 : ℤ) - j + (2 - (k + 3 - j)) = 1 - k := by ring
  calc (C j * y ^ (2 - j)) * (C (k + 3 - j) * y ^ (2 - (k + 3 - j)))
      = C j * C (k + 3 - j) * (y ^ (2 - j) * y ^ (2 - (k + 3 - j))) := by ring
    _ = C j * C (k + 3 - j) * y ^ ((2 - j) + (2 - (k + 3 - j))) := by
        rw [← zpow_add₀ hy0]
    _ = C j * C (k + 3 - j) * y ^ (1 - k) := by rw [e]

/-- E21 `D_k` formula (corrected): the paper's printed formula omits the
    factor `1/2` on the `Σ D_j D_{k+3-j}` sum (the same omission occurs
    in §5, E14). With the `1/2` the identity is exact; without it, it
    is false in general. The membership conclusion `D_k ∈ K[y]` is
    unaffected. -/
theorem e21_Dk_formula {y : F} (hy0 : y ≠ 0)
    (C D : ℤ → F) (P : ℤ → F)
    (hD : ∀ i, D i = C i * y ^ (2 - i))
    (hC3 : C 3 = y)
    {k : ℤ}
    (hP : P (k + 3) = 2 * y * C k
      + ∑ j ∈ Finset.Icc (k + 1) 2, C j * C (k + 3 - j)) :
    D k = (1 / 2) * P (k + 3) * y ^ (1 - k)
      - (1 / 2) * ∑ j ∈ Finset.Icc (k + 1) 2, D j * D (k + 3 - j) := by
  have h2y : (2 : F) * y ≠ 0 := mul_ne_zero (by norm_num : (2 : F) ≠ 0) hy0
  have hS : (∑ j ∈ Finset.Icc (k + 1) 2, C j * C (k + 3 - j)) * y ^ (1 - k)
      = ∑ j ∈ Finset.Icc (k + 1) 2, D j * D (k + 3 - j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => (e21_DD_identity hy0 C D hD j k).symm)
  have hCk : C k = (P (k + 3)
      - ∑ j ∈ Finset.Icc (k + 1) 2, C j * C (k + 3 - j)) / (2 * y) := by
    apply e19_recursion hy0
    linear_combination -hP
  rw [hD k, hCk]
  have hy1 : y ^ (2 - k) = y ^ (1 - k) * y := by
    rw [show (2 : ℤ) - k = (1 - k) + 1 by ring, zpow_add_one₀ hy0]
  rw [hy1]
  have key : (P (k + 3) - ∑ j ∈ Finset.Icc (k + 1) 2, C j * C (k + 3 - j)) / (2 * y)
        * (y ^ (1 - k) * y)
      = (1 / 2) * (P (k + 3)
          - ∑ j ∈ Finset.Icc (k + 1) 2, C j * C (k + 3 - j)) * y ^ (1 - k) := by
    field_simp
  rw [key, ← hS]
  ring

/-- E21 base case `D₃ = 1`: `D₃ = C₃ · y^{2-3} = y · y⁻¹ = 1`. -/
theorem e21_D3 {y : F} (hy0 : y ≠ 0)
    (C D : ℤ → F) (hD : ∀ i, D i = C i * y ^ (2 - i)) (hC3 : C 3 = y) :
    D 3 = 1 := by
  rw [hD 3, hC3]
  norm_num [zpow_neg_one, mul_inv_cancel₀ hy0]

end E21

/-! ### §5. E22 — the 9-equation system: coefficient expansions

`d : ℤ → R` is the coefficient function of `D̃ = φ(D)`, with `d 3 = 1`
(the `x³` coefficient), `d 2 = 0` (the φ-shift premise — see
`phi_shift_x2_vanishes` below; the paper's shift `φ(x) = x - D₂` does
NOT achieve this, it leaves `d₂ = -2D₂`), and `d i = 0` for `i ≥ 4`.
`(D̃²)_{-k}` is the coefficient of `x^{-k}` in `D̃²`, `(D̃³)_{-k}` that
in `D̃³`. The displays below are the paper's (TeX 2036–2057), with two
corrections flagged: the `(D̃²)_{-7}` display's literal `2 d_{-1} 0` is
read as `2 d_{-10}` (the Singular transcription agrees), and every
display is proved here as an identity of the finite coefficient sum,
not copied on trust.
-/

/-- Coefficient of `x^m` in `D̃²` (finite sum: `d i = 0` for `i ≥ 4`,
    and `i ≥ -11` suffices for `m ≥ -8`). -/
def D2sq {R : Type*} [CommRing R] (d : ℤ → R) (m : ℤ) : R :=
  ∑ i ∈ Finset.range 15, d (i - 11) * d (m - (i - 11))

/-- Coefficient of `x^m` in `D̃³`, via the quadratic coefficients. -/
def D3cu {R : Type*} [CommRing R] (d : ℤ → R) (m : ℤ) : R :=
  ∑ i ∈ Finset.range 15, d (i - 11) * D2sq d (m - (i - 11))

section E22exp

variable {R : Type*} [CommRing R]
variable (d : ℤ → R) (hd3 : d 3 = 1) (hd2 : d 2 = 0)
  (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0)

/-- `(D̃²)_{-k} = 0` for `k > 6` is vacuous in the truncated sum sense:
    the coefficient is `0` above the top degree `6 = 3 + 3`. -/
theorem d2sq_eq_zero_of_gt (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) {m : ℤ} (hm : 6 < m) : D2sq d m = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases hi3 : i = 14
  · subst hi3
    have e : ((14 : ℕ) : ℤ) - 11 = 3 := by norm_num
    rw [e, hd3, one_mul]
    exact hd4 _ (by omega)
  · have h1 : (i : ℤ) - 11 ≤ 2 := by omega
    have h2 : d (m - ((i : ℤ) - 11)) = 0 := hd4 _ (by omega)
    rw [h2, mul_zero]

/-- `(D̃²)_{-1} = 2 d₀d₋₁ + 2 d₁d₋₂ + 2 d₋₄` (TeX 2036). -/
theorem d2sq_neg1 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-1)
    = 2 * d 0 * d (-1) + 2 * d 1 * d (-2) + 2 * d (-4) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-2} = d₋₁² + 2 d₀d₋₂ + 2 d₁d₋₃ + 2 d₋₅` (TeX 2037). -/
theorem d2sq_neg2 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-2)
    = d (-1) ^ 2 + 2 * d 0 * d (-2) + 2 * d 1 * d (-3) + 2 * d (-5) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-3} = 2 d₋₁d₋₂ + 2 d₀d₋₃ + 2 d₁d₋₄ + 2 d₋₆` (TeX 2038). -/
theorem d2sq_neg3 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-3)
    = 2 * d (-1) * d (-2) + 2 * d 0 * d (-3) + 2 * d 1 * d (-4) + 2 * d (-6) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-4} = d₋₂² + 2 d₋₁d₋₃ + 2 d₀d₋₄ + 2 d₁d₋₅ + 2 d₋₇` (TeX 2039). -/
theorem d2sq_neg4 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-4)
    = d (-2) ^ 2 + 2 * d (-1) * d (-3) + 2 * d 0 * d (-4)
      + 2 * d 1 * d (-5) + 2 * d (-7) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-5} = 2 d₋₂d₋₃ + 2 d₋₁d₋₄ + 2 d₀d₋₅ + 2 d₁d₋₆ + 2 d₋₈` (TeX 2040). -/
theorem d2sq_neg5 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-5)
    = 2 * d (-2) * d (-3) + 2 * d (-1) * d (-4) + 2 * d 0 * d (-5)
      + 2 * d 1 * d (-6) + 2 * d (-8) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-6} = d₋₃² + 2 d₋₂d₋₄ + 2 d₋₁d₋₅ + 2 d₀d₋₆ + 2 d₁d₋₇ + 2 d₋₉`
    (TeX 2041). Displayed in §6 but EXCLUDED from the 9-equation system;
    it is used in the final combination (see `e18_final_combination`). -/
theorem d2sq_neg6 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-6)
    = d (-3) ^ 2 + 2 * d (-2) * d (-4) + 2 * d (-1) * d (-5)
      + 2 * d 0 * d (-6) + 2 * d 1 * d (-7) + 2 * d (-9) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-7} = 2 d₋₁₀ + 2 d₋₃d₋₄ + 2 d₋₂d₋₅ + 2 d₋₁d₋₆ + 2 d₀d₋₇ + 2 d₁d₋₈`
    (TeX 2042). The paper prints the first term as the literal
    `2 d_{-1} 0`; read as `2 d_{-10}` (the Singular transcription
    `2*dm10` agrees). -/
theorem d2sq_neg7 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-7)
    = 2 * d (-10) + 2 * d (-3) * d (-4) + 2 * d (-2) * d (-5)
      + 2 * d (-1) * d (-6) + 2 * d 0 * d (-7) + 2 * d 1 * d (-8) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- `(D̃²)_{-8} = 2 d₋₁₁ + d₋₄² + 2 d₋₃d₋₅ + 2 d₋₂d₋₆ + 2 d₋₁d₋₇ + 2 d₀d₋₈
    + 2 d₁d₋₉` (TeX 2043). Displayed in §6 but EXCLUDED from the
    9-equation system. -/
theorem d2sq_neg8 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d (-8)
    = 2 * d (-11) + d (-4) ^ 2 + 2 * d (-3) * d (-5) + 2 * d (-2) * d (-6)
      + 2 * d (-1) * d (-7) + 2 * d 0 * d (-8) + 2 * d 1 * d (-9) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- Auxiliary: `(D̃²)_0 = d₀² + 2 d₁d₋₁ + 2 d₋₃` (not in the paper;
    needed for the cubic displays via factorisation). -/
theorem d2sq_0 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 0
    = d 0 ^ 2 + 2 * d 1 * d (-1) + 2 * d (-3) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- Auxiliary: `(D̃²)_1 = 2 d₀d₁ + 2 d₋₂`. -/
theorem d2sq_1 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 1 = 2 * d 0 * d 1 + 2 * d (-2) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- Auxiliary: `(D̃²)_2 = d₁² + 2 d₋₁`. -/
theorem d2sq_2 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 2 = d 1 ^ 2 + 2 * d (-1) := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- Auxiliary: `(D̃²)_3 = 2 d₀`. -/
theorem d2sq_3 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 3 = 2 * d 0 := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- Auxiliary: `(D̃²)_4 = 2 d₁`. -/
theorem d2sq_4 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 4 = 2 * d 1 := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]
  ring

/-- Auxiliary: `(D̃²)_5 = 0`. -/
theorem d2sq_5 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 5 = 0 := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]

/-- Auxiliary: `(D̃²)_6 = 1`. -/
theorem d2sq_6 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 6 = 1 := by
  simp only [D2sq, Finset.sum_range_succ]
  simp [hd4, hd3, hd2]

/-- Auxiliary: `(D̃²)_7 = (D̃²)_8 = (D̃²)_9 = (D̃²)_10 = 0`. -/
theorem d2sq_7 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 7 = 0 := d2sq_eq_zero_of_gt d hd3 hd2 hd4 (by norm_num)
theorem d2sq_8 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 8 = 0 := d2sq_eq_zero_of_gt d hd3 hd2 hd4 (by norm_num)
theorem d2sq_9 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 9 = 0 := d2sq_eq_zero_of_gt d hd3 hd2 hd4 (by norm_num)
theorem d2sq_10 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D2sq d 10 = 0 := d2sq_eq_zero_of_gt d hd3 hd2 hd4 (by norm_num)

/-- `(D̃³)_{-1}` (TeX 2044, the `(Q̃)_{-1}` display): `3 d₀²d₋₁ + 3 d₁d₋₁²
    + 6 d₀d₁d₋₂ + 3 d₋₂² + 3 d₁²d₋₃ + 6 d₋₁d₋₃ + 6 d₀d₋₄ + 6 d₁d₋₅
    + 3 d₋₇`. -/
theorem d3cu_neg1 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D3cu d (-1)
    = 3 * d 0 ^ 2 * d (-1) + 3 * d 1 * d (-1) ^ 2 + 6 * d 0 * d 1 * d (-2)
      + 3 * d (-2) ^ 2 + 3 * d 1 ^ 2 * d (-3) + 6 * d (-1) * d (-3)
      + 6 * d 0 * d (-4) + 6 * d 1 * d (-5) + 3 * d (-7) := by
  simp only [D3cu, Finset.sum_range_succ]
  simp [d2sq_neg8 d hd3 hd2 hd4, d2sq_neg7 d hd3 hd2 hd4,
    d2sq_neg6 d hd3 hd2 hd4, d2sq_neg5 d hd3 hd2 hd4, d2sq_neg4 d hd3 hd2 hd4,
    d2sq_neg3 d hd3 hd2 hd4, d2sq_neg2 d hd3 hd2 hd4, d2sq_neg1 d hd3 hd2 hd4,
    d2sq_0 d hd3 hd2 hd4, d2sq_1 d hd3 hd2 hd4, d2sq_2 d hd3 hd2 hd4,
    d2sq_3 d hd3 hd2 hd4, d2sq_4 d hd3 hd2 hd4, d2sq_5 d hd3 hd2 hd4,
    d2sq_6 d hd3 hd2 hd4, d2sq_7 d hd3 hd2 hd4, d2sq_8 d hd3 hd2 hd4,
    d2sq_9 d hd3 hd2 hd4, d2sq_10 d hd3 hd2 hd4, hd2, hd3]
  ring

/-- `(D̃³)_{-2}` (TeX 2046, the `(Q̃)_{-2}` display): `3 d₀d₋₁² + 3 d₀²d₋₂
    + 6 d₁d₋₁d₋₂ + 6 d₀d₁d₋₃ + 6 d₋₂d₋₃ + 3 d₁²d₋₄ + 6 d₋₁d₋₄ + 6 d₀d₋₅
    + 6 d₁d₋₆ + 3 d₋₈`. -/
theorem d3cu_neg2 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D3cu d (-2)
    = 3 * d 0 * d (-1) ^ 2 + 3 * d 0 ^ 2 * d (-2) + 6 * d 1 * d (-1) * d (-2)
      + 6 * d 0 * d 1 * d (-3) + 6 * d (-2) * d (-3) + 3 * d 1 ^ 2 * d (-4)
      + 6 * d (-1) * d (-4) + 6 * d 0 * d (-5) + 6 * d 1 * d (-6)
      + 3 * d (-8) := by
  simp only [D3cu, Finset.sum_range_succ]
  simp [d2sq_neg8 d hd3 hd2 hd4, d2sq_neg7 d hd3 hd2 hd4,
    d2sq_neg6 d hd3 hd2 hd4, d2sq_neg5 d hd3 hd2 hd4, d2sq_neg4 d hd3 hd2 hd4,
    d2sq_neg3 d hd3 hd2 hd4, d2sq_neg2 d hd3 hd2 hd4, d2sq_neg1 d hd3 hd2 hd4,
    d2sq_0 d hd3 hd2 hd4, d2sq_1 d hd3 hd2 hd4, d2sq_2 d hd3 hd2 hd4,
    d2sq_3 d hd3 hd2 hd4, d2sq_4 d hd3 hd2 hd4, d2sq_5 d hd3 hd2 hd4,
    d2sq_6 d hd3 hd2 hd4, d2sq_7 d hd3 hd2 hd4, d2sq_8 d hd3 hd2 hd4,
    d2sq_9 d hd3 hd2 hd4, d2sq_10 d hd3 hd2 hd4, hd2, hd3]
  ring

/-- `(D̃³)_{-3}` (TeX 2048, the `(Q̃)_{-3}` display minus `λy⁸`):
    `d₋₁³ + 6 d₀d₋₁d₋₂ + 3 d₁d₋₂² + 3 d₀²d₋₃ + 6 d₁d₋₁d₋₃ + 3 d₋₃²
    + 6 d₀d₁d₋₄ + 6 d₋₂d₋₄ + 3 d₁²d₋₅ + 6 d₋₁d₋₅ + 6 d₀d₋₆ + 6 d₁d₋₇
    + 3 d₋₉`. Excluded from the 9-equation system; used in the final
    combination. -/
theorem d3cu_neg3 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D3cu d (-3)
    = d (-1) ^ 3 + 6 * d 0 * d (-1) * d (-2) + 3 * d 1 * d (-2) ^ 2
      + 3 * d 0 ^ 2 * d (-3) + 6 * d 1 * d (-1) * d (-3) + 3 * d (-3) ^ 2
      + 6 * d 0 * d 1 * d (-4) + 6 * d (-2) * d (-4) + 3 * d 1 ^ 2 * d (-5)
      + 6 * d (-1) * d (-5) + 6 * d 0 * d (-6) + 6 * d 1 * d (-7)
      + 3 * d (-9) := by
  simp only [D3cu, Finset.sum_range_succ]
  simp [d2sq_neg8 d hd3 hd2 hd4, d2sq_neg7 d hd3 hd2 hd4,
    d2sq_neg6 d hd3 hd2 hd4, d2sq_neg5 d hd3 hd2 hd4, d2sq_neg4 d hd3 hd2 hd4,
    d2sq_neg3 d hd3 hd2 hd4, d2sq_neg2 d hd3 hd2 hd4, d2sq_neg1 d hd3 hd2 hd4,
    d2sq_0 d hd3 hd2 hd4, d2sq_1 d hd3 hd2 hd4, d2sq_2 d hd3 hd2 hd4,
    d2sq_3 d hd3 hd2 hd4, d2sq_4 d hd3 hd2 hd4, d2sq_5 d hd3 hd2 hd4,
    d2sq_6 d hd3 hd2 hd4, d2sq_7 d hd3 hd2 hd4, d2sq_8 d hd3 hd2 hd4,
    d2sq_9 d hd3 hd2 hd4, d2sq_10 d hd3 hd2 hd4, hd2, hd3]
  ring

/-- `(D̃³)_{-4}` (TeX 2050, the `(Q̃)_{-4}` display minus `F_{-4}y¹⁰`):
    `3 d₋₁₀ + 3 d₋₁²d₋₂ + 3 d₀d₋₂² + 6 d₀d₋₁d₋₃ + 6 d₁d₋₂d₋₃ + 3 d₀²d₋₄
    + 6 d₁d₋₁d₋₄ + 6 d₋₃d₋₄ + 6 d₀d₁d₋₅ + 6 d₋₂d₋₅ + 3 d₁²d₋₆
    + 6 d₋₁d₋₆ + 6 d₀d₋₇ + 6 d₁d₋₈`. -/
theorem d3cu_neg4 (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) : D3cu d (-4)
    = 3 * d (-10) + 3 * d (-1) ^ 2 * d (-2) + 3 * d 0 * d (-2) ^ 2
      + 6 * d 0 * d (-1) * d (-3) + 6 * d 1 * d (-2) * d (-3)
      + 3 * d 0 ^ 2 * d (-4) + 6 * d 1 * d (-1) * d (-4)
      + 6 * d (-3) * d (-4) + 6 * d 0 * d 1 * d (-5) + 6 * d (-2) * d (-5)
      + 3 * d 1 ^ 2 * d (-6) + 6 * d (-1) * d (-6) + 6 * d 0 * d (-7)
      + 6 * d 1 * d (-8) := by
  simp only [D3cu, Finset.sum_range_succ]
  simp [d2sq_neg8 d hd3 hd2 hd4, d2sq_neg7 d hd3 hd2 hd4,
    d2sq_neg6 d hd3 hd2 hd4, d2sq_neg5 d hd3 hd2 hd4, d2sq_neg4 d hd3 hd2 hd4,
    d2sq_neg3 d hd3 hd2 hd4, d2sq_neg2 d hd3 hd2 hd4, d2sq_neg1 d hd3 hd2 hd4,
    d2sq_0 d hd3 hd2 hd4, d2sq_1 d hd3 hd2 hd4, d2sq_2 d hd3 hd2 hd4,
    d2sq_3 d hd3 hd2 hd4, d2sq_4 d hd3 hd2 hd4, d2sq_5 d hd3 hd2 hd4,
    d2sq_6 d hd3 hd2 hd4, d2sq_7 d hd3 hd2 hd4, d2sq_8 d hd3 hd2 hd4,
    d2sq_9 d hd3 hd2 hd4, d2sq_10 d hd3 hd2 hd4, hd2, hd3]
  ring

end E22exp
/-! ### §5 (continued). E22 — principal equation via the certificate

The identity below is transcribed verbatim from
`singular/d1_singular_cert_s6_2026-11-05.sing` (Part 11/12 D3
certificate, CERT_DIFF = 0, CERT_IS_ZERO = 1 in Singular 4.3.1).
Lean's `linear_combination` re-verifies it by `ring` here; the
Singular run is the second independent tool. -/

/-- E22 principal-equation certificate: if the 9 displayed equations
    hold, then `dm1 * (9 y^9 d1 dm1^6 + y^27 + 27 d0 dm1^9) = 0`.
    The 9th hypothesis is the doubled `(Q̃)_{-4}` equation
    (`2 * Q4 = 0`, i.e. `6 dm10 + … + y^9 = 0`), as in the cert file. -/
theorem s6_principal_certificate {R : Type*} [CommRing R]
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 y : R)
    (hD21 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD22 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD23 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD24 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD25 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD27 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7 + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8 = 0)
    (hQ4x2 : 6 * dm10 + 6 * dm1 ^ 2 * dm2 + 6 * d0 * dm2 ^ 2 + 12 * d0 * dm1 * dm3 + 12 * d1 * dm2 * dm3 + 6 * d0 ^ 2 * dm4 + 12 * d1 * dm1 * dm4 + 12 * dm3 * dm4 + 12 * d0 * d1 * dm5 + 12 * dm2 * dm5 + 6 * d1 ^ 2 * dm6 + 12 * dm1 * dm6 + 12 * d0 * dm7 + 12 * d1 * dm8 + y ^ 9 = 0)
    : dm1 * (9 * y ^ 9 * d1 * dm1 ^ 6 + y ^ 27 + 27 * d0 * dm1 ^ 9) = 0 := by
  linear_combination (-27 * d0 ^ 2 * d1 * dm1 ^ 7 - 27 * d0 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 9 * d0 ^ 2 * dm1 ^ 3 * dm2 * y ^ 9 - 3 * d0 ^ 2 * dm1 * y ^ 18 - 27 * d0 * dm1 ^ 7 * dm2 - 27 * d1 ^ 2 * dm1 ^ 8 - 27 * d1 * dm1 ^ 7 * dm3 - 27 * d1 * dm1 ^ 6 * dm2 ^ 2 - 9 * d1 * dm1 ^ 4 * dm2 * y ^ 9 - 3 * d1 * dm1 ^ 2 * y ^ 18 + 27 * dm1 ^ 9 - 27 * dm1 ^ 5 * dm2 ^ 2 * dm3 - 9 * dm1 ^ 3 * dm2 * dm3 * y ^ 9 - 3 * dm1 * dm3 * y ^ 18) * hD21 + (-54 * d0 * d1 ^ 2 * dm1 ^ 7 - 54 * d0 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * d0 * d1 * dm1 ^ 3 * dm2 * y ^ 9 - 6 * d0 * d1 * dm1 * y ^ 18 + 27 * d0 * dm1 ^ 8 - 54 * d1 * dm1 ^ 7 * dm2 - 27 * dm1 ^ 5 * dm2 ^ 3 - 9 * dm1 ^ 3 * dm2 ^ 2 * y ^ 9 - 3 * dm1 * dm2 * y ^ 18) * hD22 + (-27 * d1 ^ 3 * dm1 ^ 7 - 27 * d1 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 9 * d1 ^ 2 * dm1 ^ 3 * dm2 * y ^ 9 - 3 * d1 ^ 2 * dm1 * y ^ 18 - 27 * dm1 ^ 6 * dm2 ^ 2 - 9 * dm1 ^ 4 * dm2 * y ^ 9 - 3 * dm1 ^ 2 * y ^ 18) * hD23 + (-54 * d0 * d1 * dm1 ^ 7 - 54 * d0 * dm1 ^ 5 * dm2 ^ 2 - 18 * d0 * dm1 ^ 3 * dm2 * y ^ 9 - 6 * d0 * dm1 * y ^ 18 - 27 * dm1 ^ 7 * dm2) * hD24 + (-54 * d1 ^ 2 * dm1 ^ 7 - 54 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * d1 * dm1 ^ 3 * dm2 * y ^ 9 - 6 * d1 * dm1 * y ^ 18 + 27 * dm1 ^ 8) * hD25 + (-27 * d1 * dm1 ^ 7 - 27 * dm1 ^ 5 * dm2 ^ 2 - 9 * dm1 ^ 3 * dm2 * y ^ 9 - 3 * dm1 * y ^ 18) * hD27 + (18 * d0 * d1 * dm1 ^ 7 + 18 * d0 * dm1 ^ 5 * dm2 ^ 2 + 6 * d0 * dm1 ^ 3 * dm2 * y ^ 9 + 2 * d0 * dm1 * y ^ 18 + 18 * dm1 ^ 7 * dm2) * hQ1 + (18 * d1 ^ 2 * dm1 ^ 7 + 18 * d1 * dm1 ^ 5 * dm2 ^ 2 + 6 * d1 * dm1 ^ 3 * dm2 * y ^ 9 + 2 * d1 * dm1 * y ^ 18 - 18 * dm1 ^ 8) * hQ2 + (9 * d1 * dm1 ^ 7 + 9 * dm1 ^ 5 * dm2 ^ 2 + 3 * dm1 ^ 3 * dm2 * y ^ 9 + dm1 * y ^ 18) * hQ4x2

/-! ### §6. E22 — the φ-shift flag, and the system-to-principal assembly -/

/-- **FLAG (both §5 and §6):** the paper's shift `φ(x) = x - D₂` does NOT
    kill the `x²` term. For `D = x³ + D₂x² + D₁x + D₀` (truncated),
    `φ(D)` has `x²`-coefficient `-2D₂`, not `0`:
    `(x-a)³ + a(x-a)² = x³ - 2a·x² + a²·x`. The displays in §5/§6
    (which omit all `d₂` terms) therefore rest on `d₂ = 0` as an
    additional premise, not on the stated shift. -/
theorem phi_shift_x2_paper {R : Type*} [CommRing R] (x a : R) :
    (x - a) ^ 3 + a * (x - a) ^ 2 = x ^ 3 - 2 * a * x ^ 2 + a ^ 2 * x := by ring

/-- The shift that DOES kill the `x²` term is `x ↦ x - D₂/3`:
    `(x-a/3)³ + a(x-a/3)² = x³ - (a²/3)x + 2a³/27`. -/
theorem phi_shift_x2_corrected {F : Type*} [Field F] [CharZero F] (x a : F) :
    (x - a / 3) ^ 3 + a * (x - a / 3) ^ 2
      = x ^ 3 - (a ^ 2 / 3) * x + 2 * a ^ 3 / 27 := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  field_simp
  ring

/-- The φ-shift premise, carried explicitly: the `x²`-coefficient of
    `D̃ = φ(D)` vanishes. The paper asserts this from `φ(x) = x - D₂`;
    that shift gives `-2D₂` (see `phi_shift_x2_paper`), so the vanishing
    is recorded here as the named premise `phi_shift_x2_vanishes`,
    not derived. -/
def phi_shift_x2_vanishes {R : Type*} [CommRing R] (d : ℤ → R) : Prop := d 2 = 0

section E22asm

variable {F : Type*} [Field F] [CharZero F]

/-- E22: the 9 displayed equations from the vanishing of the
    `(D̃²)_{-k}`, `(D̃³)_{-j}` coefficients (i.e. from
    `φ(P̂), φ(Q̂) ∈ K[x,y]`). The `(Q̃)_{-3}` equation carries `+ λy⁸`,
    the `(Q̃)_{-4}` equation carries `+ F_{-4}y¹⁰ = (1/2)y⁹` (E23);
    the last conjunct is the doubled `(Q̃)_{-4}` form used by the
    certificate. -/
theorem e22_displays_from_vanishing (d : ℤ → F) (hd3 : d 3 = 1) (hd2 : d 2 = 0)
    (hd4 : ∀ i : ℤ, 4 ≤ i → d i = 0) (lam y : F)
    (hD2 : ∀ k : ℤ, 1 ≤ k → k ≤ 8 → D2sq d (-k) = 0)
    (hD31 : D3cu d (-1) = 0) (hD32 : D3cu d (-2) = 0)
    (hD33 : D3cu d (-3) + lam * y ^ 8 = 0)
    (hD34 : D3cu d (-4) + (1 / 2 : F) * y ^ 9 = 0) :
    (2 * d 0 * d (-1) + 2 * d 1 * d (-2) + 2 * d (-4) = 0) ∧
    (d (-1) ^ 2 + 2 * d 0 * d (-2) + 2 * d 1 * d (-3) + 2 * d (-5) = 0) ∧
    (2 * d (-1) * d (-2) + 2 * d 0 * d (-3) + 2 * d 1 * d (-4) + 2 * d (-6) = 0) ∧
    (d (-2) ^ 2 + 2 * d (-1) * d (-3) + 2 * d 0 * d (-4)
      + 2 * d 1 * d (-5) + 2 * d (-7) = 0) ∧
    (2 * d (-2) * d (-3) + 2 * d (-1) * d (-4) + 2 * d 0 * d (-5)
      + 2 * d 1 * d (-6) + 2 * d (-8) = 0) ∧
    (2 * d (-10) + 2 * d (-3) * d (-4) + 2 * d (-2) * d (-5)
      + 2 * d (-1) * d (-6) + 2 * d 0 * d (-7) + 2 * d 1 * d (-8) = 0) ∧
    (3 * d 0 ^ 2 * d (-1) + 3 * d 1 * d (-1) ^ 2 + 6 * d 0 * d 1 * d (-2)
      + 3 * d (-2) ^ 2 + 3 * d 1 ^ 2 * d (-3) + 6 * d (-1) * d (-3)
      + 6 * d 0 * d (-4) + 6 * d 1 * d (-5) + 3 * d (-7) = 0) ∧
    (3 * d 0 * d (-1) ^ 2 + 3 * d 0 ^ 2 * d (-2) + 6 * d 1 * d (-1) * d (-2)
      + 6 * d 0 * d 1 * d (-3) + 6 * d (-2) * d (-3) + 3 * d 1 ^ 2 * d (-4)
      + 6 * d (-1) * d (-4) + 6 * d 0 * d (-5) + 6 * d 1 * d (-6)
      + 3 * d (-8) = 0) ∧
    (6 * d (-10) + 6 * d (-1) ^ 2 * d (-2) + 6 * d 0 * d (-2) ^ 2
      + 12 * d 0 * d (-1) * d (-3) + 12 * d 1 * d (-2) * d (-3)
      + 6 * d 0 ^ 2 * d (-4) + 12 * d 1 * d (-1) * d (-4)
      + 12 * d (-3) * d (-4) + 12 * d 0 * d 1 * d (-5) + 12 * d (-2) * d (-5)
      + 6 * d 1 ^ 2 * d (-6) + 12 * d (-1) * d (-6) + 12 * d 0 * d (-7)
      + 12 * d 1 * d (-8) + y ^ 9 = 0) := by
  have e1 := hD2 1 (by norm_num) (by norm_num)
  have e2 := hD2 2 (by norm_num) (by norm_num)
  have e3 := hD2 3 (by norm_num) (by norm_num)
  have e4 := hD2 4 (by norm_num) (by norm_num)
  have e5 := hD2 5 (by norm_num) (by norm_num)
  have e7 := hD2 7 (by norm_num) (by norm_num)
  rw [d2sq_neg1 d hd3 hd2 hd4] at e1
  rw [d2sq_neg2 d hd3 hd2 hd4] at e2
  rw [d2sq_neg3 d hd3 hd2 hd4] at e3
  rw [d2sq_neg4 d hd3 hd2 hd4] at e4
  rw [d2sq_neg5 d hd3 hd2 hd4] at e5
  rw [d2sq_neg7 d hd3 hd2 hd4] at e7
  rw [d3cu_neg1 d hd3 hd2 hd4] at hD31
  rw [d3cu_neg2 d hd3 hd2 hd4] at hD32
  rw [d3cu_neg4 d hd3 hd2 hd4] at hD34
  refine ⟨e1, e2, e3, e4, e5, e7, hD31, hD32, ?_⟩
  linear_combination 2 * hD34

/-- E22 principal equation (TeX 2058) from the 9 displayed equations:
    `9 y⁹ d₁ (d₋₁)⁶ + y²⁷ + 27 d₀ (d₋₁)⁹ = 0`, for `d₋₁ ≠ 0`. -/
theorem s6_principal_eq {K : Type*} [Field K] [CharZero K]
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 : Polynomial K)
    (hD21 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD22 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD23 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD24 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD25 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD27 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6
      + 2 * d0 * dm7 + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2
      + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4
      + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2
      + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4
      + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8 = 0)
    (hQ4x2 : 6 * dm10 + 6 * dm1 ^ 2 * dm2 + 6 * d0 * dm2 ^ 2
      + 12 * d0 * dm1 * dm3 + 12 * d1 * dm2 * dm3 + 6 * d0 ^ 2 * dm4
      + 12 * d1 * dm1 * dm4 + 12 * dm3 * dm4 + 12 * d0 * d1 * dm5
      + 12 * dm2 * dm5 + 6 * d1 ^ 2 * dm6 + 12 * dm1 * dm6 + 12 * d0 * dm7
      + 12 * d1 * dm8 + Polynomial.X ^ 9 = 0)
    (hdm1 : dm1 ≠ 0) :
    9 * Polynomial.X ^ 9 * d1 * dm1 ^ 6 + Polynomial.X ^ 27
      + 27 * d0 * dm1 ^ 9 = 0 := by
  have h := s6_principal_certificate d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10
    Polynomial.X hD21 hD22 hD23 hD24 hD25 hD27 hQ1 hQ2 hQ4x2
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hdm1
  · exact h1

end E22asm

/-! ### §7. E18 — `k = 2` and the non-square contradiction: degree lemmas -/

section E18deg

variable {K : Type*} [Field K] [CharZero K]

/-- If `b` has strictly greater `natDegree` than `a` and `c`, and `b ≠ 0`
    has positive degree, then `a + b + c ≠ 0` (the leading term of `b`
    survives). -/
theorem poly_add_ne_zero_of_degree {a b c : Polynomial K}
    (hab : a.natDegree < b.natDegree) (hcb : c.natDegree < b.natDegree)
    (hb : b ≠ 0) (hbdeg : 0 < b.natDegree) : a + b + c ≠ 0 := by
  intro hzero
  have h1 : (a + c).natDegree < b.natDegree := by
    calc (a + c).natDegree ≤ max a.natDegree c.natDegree :=
          Polynomial.natDegree_add_le _ _
      _ < b.natDegree := max_lt hab hcb
  have h2 : ((a + c) + b).natDegree = b.natDegree :=
    Polynomial.natDegree_add_eq_right_of_natDegree_lt h1
  have h3 : (a + b + c) = (a + c) + b := by ring
  rw [← h3, hzero] at h2
  simp only [Polynomial.natDegree_zero] at h2
  omega

/-- E18 `k = 2`: with `d₋₁ = α·y^k` (`α ≠ 0`), `deg d₀ = 9`,
    `deg d₁ = 6`, the principal equation forces `k = 2`. At `k < 2` the
    `y²⁷` term dominates; at `k > 2` the `27 d₀ (d₋₁)⁹` term dominates. -/
theorem s6_k2 (d0 d1 : Polynomial K) (α : K) (hα : α ≠ 0) (k : ℕ)
    (hd0 : d0.natDegree = 9) (hd1 : d1.natDegree = 6)
    (hprin : 9 * Polynomial.X ^ 9 * d1 * (Polynomial.C α * Polynomial.X ^ k) ^ 6
        + Polynomial.X ^ 27
        + 27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9 = 0) :
    k = 2 := by
  by_cases hk : k = 2
  · exact hk
  · exfalso
    have hαC : (Polynomial.C α : Polynomial K) ≠ 0 := by simp [hα]
    have hXk : (Polynomial.X ^ k : Polynomial K) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have hdm1 : (Polynomial.C α * Polynomial.X ^ k : Polynomial K) ≠ 0 :=
      mul_ne_zero hαC hXk
    have hdm1deg : (Polynomial.C α * Polynomial.X ^ k : Polynomial K).natDegree = k := by
      rw [Polynomial.natDegree_mul hαC hXk, Polynomial.natDegree_C,
        Polynomial.natDegree_X_pow]
      simp
    have hd0ne : d0 ≠ 0 := by
      intro h; rw [h] at hd0; simp at hd0
    have h27 : (27 : Polynomial K) ≠ 0 := by
      rw [← Polynomial.C_ofNat]
      exact Polynomial.C_ne_zero.mpr (by norm_num)
    have h9deg : (9 : Polynomial K).natDegree = 0 := by
      rw [← Polynomial.C_ofNat]; exact Polynomial.natDegree_C _
    have h27deg : (27 : Polynomial K).natDegree = 0 := by
      rw [← Polynomial.C_ofNat]; exact Polynomial.natDegree_C _
    -- term degree bounds / values
    have hT1 : (9 * Polynomial.X ^ 9 * d1
        * (Polynomial.C α * Polynomial.X ^ k) ^ 6 : Polynomial K).natDegree
        ≤ 15 + 6 * k := by
      have e1 := Polynomial.natDegree_mul_le (p := (9 * Polynomial.X ^ 9 * d1 : Polynomial K))
        (q := ((Polynomial.C α * Polynomial.X ^ k) ^ 6))
      have e2 := Polynomial.natDegree_mul_le (p := (9 * Polynomial.X ^ 9 : Polynomial K)) (q := d1)
      have e3 := Polynomial.natDegree_mul_le (p := (9 : Polynomial K)) (q := (Polynomial.X ^ 9))
      have e4 : ((Polynomial.C α * Polynomial.X ^ k) ^ 6 : Polynomial K).natDegree
          = 6 * k := by
        rw [Polynomial.natDegree_pow, hdm1deg]
      have hX9 : (Polynomial.X ^ 9 : Polynomial K).natDegree = 9 :=
        Polynomial.natDegree_X_pow 9
      omega
    have hT3 : (27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9
        : Polynomial K).natDegree = 9 + 9 * k := by
      have e1 : (27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9 : Polynomial K)
          = (27 : Polynomial K) * (d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9) := by
        ring
      rw [e1, Polynomial.natDegree_mul h27 (mul_ne_zero hd0ne (pow_ne_zero 9 hdm1)),
        Polynomial.natDegree_mul hd0ne (pow_ne_zero 9 hdm1),
        Polynomial.natDegree_pow, hdm1deg, hd0, h27deg]
      simp
    have hT3ne : (27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9
        : Polynomial K) ≠ 0 := by
      intro h; rw [h] at hT3
      simp only [Polynomial.natDegree_zero] at hT3
      omega
    have hT2 : (Polynomial.X ^ 27 : Polynomial K).natDegree = 27 :=
      Polynomial.natDegree_X_pow 27
    by_cases hlt : k < 2
    · -- the y^27 term dominates
      exact poly_add_ne_zero_of_degree
        (a := 9 * Polynomial.X ^ 9 * d1 * (Polynomial.C α * Polynomial.X ^ k) ^ 6)
        (b := Polynomial.X ^ 27)
        (c := 27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9)
        (by omega) (by omega) (pow_ne_zero _ Polynomial.X_ne_zero) (by omega) hprin
    · -- k > 2: the 27 d0 (d_{-1})^9 term dominates
      have hgt : 2 < k := by omega
      have hne : (9 * Polynomial.X ^ 9 * d1 * (Polynomial.C α * Polynomial.X ^ k) ^ 6
          + 27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9
          + Polynomial.X ^ 27 : Polynomial K) ≠ 0 :=
        poly_add_ne_zero_of_degree
          (a := 9 * Polynomial.X ^ 9 * d1 * (Polynomial.C α * Polynomial.X ^ k) ^ 6)
          (b := 27 * d0 * (Polynomial.C α * Polynomial.X ^ k) ^ 9)
          (c := Polynomial.X ^ 27)
          (by omega) (by omega) hT3ne (by omega)
      apply hne
      linear_combination hprin

end E18deg

/-! ### §8. E18 — the final combination, the square identity, the non-square -/

section E18end

variable {K : Type*} [Field K] [CharZero K]

/-- E18 final combination: `2(Q̃)_{-3} - 3((D̃²)_{-6} + d₁(D̃²)_{-4}
    + d₀(D̃²)_{-3} + d₋₁(D̃²)_{-2} + d₋₂(D̃²)_{-1})` equals
    `-(d₋₁)³ - 6d₀d₋₁d₋₂ - 3d₁(d₋₂)² + 3(d₋₃)² + 2λy⁸` (the `+2λy⁸`
    from `(Q̃)_{-3} = (D̃³)_{-3} + λy⁸`). Pure `ring` identity among
    the displays, given the system equations. -/
theorem e18_final_combination
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm9 : Polynomial K)
    (lam : K)
    (hD21 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD22 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD23 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD24 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD26 : dm3 ^ 2 + 2 * dm2 * dm4 + 2 * dm1 * dm5 + 2 * d0 * dm6
      + 2 * d1 * dm7 + 2 * dm9 = 0)
    (hQ3 : dm1 ^ 3 + 6 * d0 * dm1 * dm2 + 3 * d1 * dm2 ^ 2
      + 3 * d0 ^ 2 * dm3 + 6 * d1 * dm1 * dm3 + 3 * dm3 ^ 2
      + 6 * d0 * d1 * dm4 + 6 * dm2 * dm4 + 3 * d1 ^ 2 * dm5
      + 6 * dm1 * dm5 + 6 * d0 * dm6 + 6 * d1 * dm7 + 3 * dm9
      + Polynomial.C lam * Polynomial.X ^ 8 = 0) :
    -(dm1) ^ 3 - 6 * d0 * dm1 * dm2 - 3 * d1 * dm2 ^ 2 + 3 * dm3 ^ 2
      + 2 * Polynomial.C lam * Polynomial.X ^ 8 = 0 := by
  linear_combination 2 * hQ3 - 3 * hD26 - 3 * d1 * hD24 - 3 * d0 * hD23
    - 3 * dm1 * hD22 - 3 * dm2 * hD21

/-- E18 square identity, field version: substituting
    `d₁ = (-27 d₀ dm1⁹ - y²⁷)/(9 dm1⁶ y⁹)`,
    `d₋₂ = y⁹/(3 dm1²)`, `d₋₃ = 3 d₀ dm1⁴/(2 y⁹)` and `dm1 = α y²`
    into the final combination equation gives
    `(27 α⁹ d₀ - 2 y⁹)² = 108 α¹⁰ (α³ y⁸ - 2 λ y¹⁰)`.
    The multiplier is `108 α¹⁰ y²` (verified by hand; `ring` checks it
    after clearing denominators). -/
theorem square_identity_field {F : Type*} [Field F] [CharZero F]
    (d0 d1 dm1 dm2 dm3 y α lam : F)
    (hα : α ≠ 0) (hy : y ≠ 0) (hdm1 : dm1 ≠ 0)
    (hdm1form : dm1 = α * y ^ 2)
    (hprin : 9 * y ^ 9 * d1 * dm1 ^ 6 + y ^ 27 + 27 * d0 * dm1 ^ 9 = 0)
    (hid2 : 3 * dm1 ^ 2 * dm2 = y ^ 9)
    (hid3 : 2 * dm3 * y ^ 9 = 3 * d0 * dm1 ^ 4)
    (hfin : -(dm1) ^ 3 - 6 * d0 * dm1 * dm2 - 3 * d1 * dm2 ^ 2 + 3 * dm3 ^ 2
      + 2 * lam * y ^ 8 = 0) :
    (27 * α ^ 9 * d0 - 2 * y ^ 9) ^ 2
      = 108 * α ^ 10 * (α ^ 3 * y ^ 8 - 2 * lam * y ^ 10) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have hd2 : dm2 = y ^ 9 / (3 * dm1 ^ 2) := by
    rw [eq_div_iff (mul_ne_zero h3 (pow_ne_zero 2 hdm1))]
    linear_combination hid2
  have hd3 : dm3 = 3 * d0 * dm1 ^ 4 / (2 * y ^ 9) := by
    rw [eq_div_iff (mul_ne_zero h2 (pow_ne_zero 9 hy))]
    linear_combination hid3
  have hd1 : d1 = (-y ^ 27 - 27 * d0 * dm1 ^ 9) / (9 * y ^ 9 * dm1 ^ 6) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero h9 (pow_ne_zero 9 hy)) (pow_ne_zero 6 hdm1))]
    linear_combination hprin
  have key : (108 * α ^ 10 * y ^ 2)
        * (-(dm1) ^ 3 - 6 * d0 * dm1 * dm2 - 3 * d1 * dm2 ^ 2 + 3 * dm3 ^ 2
          + 2 * lam * y ^ 8)
      = (27 * α ^ 9 * d0 - 2 * y ^ 9) ^ 2
        - 108 * α ^ 10 * (α ^ 3 * y ^ 8 - 2 * lam * y ^ 10) := by
    rw [hd2, hd3, hd1, hdm1form]
    field_simp
    ring
  rw [hfin, mul_zero] at key
  linear_combination -key

/-- Helper: if `S² = X^{2m} · W` then `X^m ∣ S` (iterate the prime
    step `X ∣ S² → X ∣ S`). -/
theorem X_pow_dvd_of_sq {S W : Polynomial K} {m : ℕ}
    (h : S ^ 2 = Polynomial.X ^ (2 * m) * W) : Polynomial.X ^ m ∣ S := by
  induction m generalizing S with
  | zero => simp
  | succ m ih =>
      have h1 : (Polynomial.X : Polynomial K) ∣ Polynomial.X ^ (2 * (m + 1)) := by
        simpa using pow_dvd_pow Polynomial.X (show 1 ≤ 2 * (m + 1) by omega)
      have h2 : Polynomial.X ∣ S ^ 2 := by
        rw [h]; exact dvd_trans h1 (dvd_mul_right _ _)
      have h3 : Polynomial.X ∣ S := Polynomial.prime_X.dvd_of_dvd_pow h2
      obtain ⟨S₁, hS₁⟩ := h3
      have h4 : S₁ ^ 2 = Polynomial.X ^ (2 * m) * W := by
        have h5 : (Polynomial.X * S₁) ^ 2
            = Polynomial.X ^ (2 * (m + 1)) * W := by
          rw [← hS₁]; exact h
        rw [mul_pow] at h5
        have e : (2 : ℕ) * (m + 1) = 2 + 2 * m := by ring
        rw [e, pow_add] at h5
        have h6 : Polynomial.X ^ 2 * S₁ ^ 2
            = Polynomial.X ^ 2 * (Polynomial.X ^ (2 * m) * W) := by
          linear_combination h5
        exact mul_left_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) h6
      have h7 : Polynomial.X ^ m ∣ S₁ := ih h4
      obtain ⟨S₂, hS₂⟩ := h7
      exact ⟨S₂, by rw [hS₁, hS₂, pow_succ]; ring⟩

/-- E18 non-square contradiction: `(27 α⁹ d₀ - 2 y⁹)² = 108 α¹⁰ (α³ y⁸
    - 2 λ y¹⁰)` is impossible for `α, λ ≠ 0`, since the right side is
    `y⁸` times a quadratic with nonzero constant term, and a square
    divided by `y⁸` would have to be a square of a linear polynomial
    `a + by` with `2ab = 0`, `a² ≠ 0`, `b² ≠ 0` — impossible. -/
theorem s6_nonsquare (d0 : Polynomial K) (α lam : K) (hα : α ≠ 0) (hlam : lam ≠ 0)
    (h : (27 * Polynomial.C α ^ 9 * d0 - 2 * Polynomial.X ^ 9) ^ 2
      = 108 * Polynomial.C α ^ 10
        * (Polynomial.C α ^ 3 * Polynomial.X ^ 8
          - 2 * Polynomial.C lam * Polynomial.X ^ 10)) :
    False := by
  set S := 27 * Polynomial.C α ^ 9 * d0 - 2 * Polynomial.X ^ 9 with hS
  have hW : (108 * Polynomial.C α ^ 10
        * (Polynomial.C α ^ 3 * Polynomial.X ^ 8
          - 2 * Polynomial.C lam * Polynomial.X ^ 10) : Polynomial K)
      = Polynomial.X ^ 8 * (108 * Polynomial.C α ^ 10
        * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)) := by
    ring
  rw [hW] at h
  obtain ⟨S₄, hS₄⟩ := X_pow_dvd_of_sq (m := 4) h
  have hS4sq : S₄ ^ 2 = 108 * Polynomial.C α ^ 10
      * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2) := by
    have h5 : (Polynomial.X ^ 4 * S₄) ^ 2
        = Polynomial.X ^ 8 * (108 * Polynomial.C α ^ 10
          * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)) := by
      rw [← hS₄]; exact h
    rw [mul_pow, ← pow_mul] at h5
    have e : (4 : ℕ) * 2 = 8 := by norm_num
    rw [e] at h5
    exact mul_left_cancel₀ (pow_ne_zero 8 Polynomial.X_ne_zero) h5
  -- `S₄` has degree 1
  have hW0deg : (108 * Polynomial.C α ^ 10
      * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)
      : Polynomial K).natDegree = 2 := by
    compute_degree!
  have hS4ne : S₄ ≠ 0 := by
    intro h0
    rw [h0] at hS4sq
    rw [show ((0 : Polynomial K) ^ 2) = 0 by simp] at hS4sq
    rw [← hS4sq] at hW0deg
    simp at hW0deg
  have hdeg : S₄.natDegree = 1 := by
    have h1 : (S₄ ^ 2).natDegree = 2 * S₄.natDegree := Polynomial.natDegree_pow S₄ 2
    rw [hS4sq, hW0deg] at h1
    omega
  -- `S₄ = s₀ + s₁·X`
  have hS4form : S₄ = Polynomial.C (S₄.coeff 0)
      + Polynomial.C (S₄.coeff 1) * Polynomial.X := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow S₄, hdeg]
    simp [Finset.sum_range_succ]
  -- coefficients of `W₀ = 108 C α¹⁰ (C α³ - 2 C λ X²)`
  have hW0 : (108 * Polynomial.C α ^ 10
      * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)
      : Polynomial K)
      = Polynomial.C (108 * α ^ 10)
        * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2) := by
    rw [show (108 : Polynomial K) = Polynomial.C (108 : K) by rw [Polynomial.C_ofNat],
      ← Polynomial.C_pow, ← Polynomial.C_mul]
  -- coefficients of `Q = C α³ - 2 C λ X²` (explicit, avoiding `simp`'s
  -- `C_pow` splitting of `(C α)^n`)
  have hC2lam : (2 * Polynomial.C lam * Polynomial.X ^ 2 : Polynomial K)
      = Polynomial.C (2 * lam) * Polynomial.X ^ 2 := by
    rw [← Polynomial.C_ofNat, ← Polynomial.C_mul]
  have hQc0 : (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2
      : Polynomial K).coeff 0 = α ^ 3 := by
    rw [Polynomial.coeff_sub]
    have e1 : (Polynomial.C α ^ 3 : Polynomial K).coeff 0 = α ^ 3 := by
      rw [← Polynomial.C_pow, Polynomial.coeff_C]; simp
    have e2 : (2 * Polynomial.C lam * Polynomial.X ^ 2 : Polynomial K).coeff 0 = 0 := by
      rw [hC2lam, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp
    rw [e1, e2, sub_zero]
  have hQc1 : (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2
      : Polynomial K).coeff 1 = 0 := by
    rw [Polynomial.coeff_sub]
    have e1 : (Polynomial.C α ^ 3 : Polynomial K).coeff 1 = 0 := by
      rw [← Polynomial.C_pow, Polynomial.coeff_C]; simp
    have e2 : (2 * Polynomial.C lam * Polynomial.X ^ 2 : Polynomial K).coeff 1 = 0 := by
      rw [hC2lam, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp
    rw [e1, e2, sub_zero]
  have hQc2 : (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2
      : Polynomial K).coeff 2 = -2 * lam := by
    rw [Polynomial.coeff_sub]
    have e1 : (Polynomial.C α ^ 3 : Polynomial K).coeff 2 = 0 := by
      rw [← Polynomial.C_pow, Polynomial.coeff_C]; simp
    have e2 : (2 * Polynomial.C lam * Polynomial.X ^ 2 : Polynomial K).coeff 2 = 2 * lam := by
      rw [hC2lam, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp
    rw [e1, e2]; ring
  have hW0c0 : (108 * Polynomial.C α ^ 10
      * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)
      : Polynomial K).coeff 0 = 108 * α ^ 13 := by
    rw [hW0, Polynomial.coeff_C_mul, hQc0]
    ring
  have hW0c1 : (108 * Polynomial.C α ^ 10
      * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)
      : Polynomial K).coeff 1 = 0 := by
    rw [hW0, Polynomial.coeff_C_mul, hQc1, mul_zero]
  have hW0c2 : (108 * Polynomial.C α ^ 10
      * (Polynomial.C α ^ 3 - 2 * Polynomial.C lam * Polynomial.X ^ 2)
      : Polynomial K).coeff 2 = -216 * α ^ 10 * lam := by
    rw [hW0, Polynomial.coeff_C_mul, hQc2]
    ring
  -- coefficients of `S₄² = W₀` (antidiagonal sums evaluated by `decide`)
  have hanti1 : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := by
    decide
  have hanti2 : Finset.HasAntidiagonal.antidiagonal 2
      = {(0, 2), (1, 1), (2, 0)} := by decide
  have hc0 : S₄.coeff 0 ^ 2 = 108 * α ^ 13 := by
    have h0 := congrArg (fun p : Polynomial K => p.coeff 0) hS4sq
    rw [show S₄ ^ 2 = S₄ * S₄ by ring] at h0
    rw [hW0c0] at h0
    simp only [Polynomial.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton] at h0
    linear_combination h0
  have hs0 : S₄.coeff 0 ≠ 0 := by
    intro h0
    rw [h0] at hc0
    have hne : (108 : K) * α ^ 13 ≠ 0 := by
      apply mul_ne_zero _ (pow_ne_zero _ hα)
      norm_num
    exact hne (by rw [← hc0]; simp)
  have hc1 : 2 * S₄.coeff 0 * S₄.coeff 1 = 0 := by
    have h1 := congrArg (fun p : Polynomial K => p.coeff 1) hS4sq
    rw [show S₄ ^ 2 = S₄ * S₄ by ring] at h1
    rw [hW0c1] at h1
    simp [Polynomial.coeff_mul, hanti1] at h1
    linear_combination h1
  have hs1 : S₄.coeff 1 = 0 := by
    rcases mul_eq_zero.mp hc1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact absurd h hs0
    · exact h
  have hc2 : S₄.coeff 1 ^ 2 = -216 * α ^ 10 * lam := by
    have h2 := congrArg (fun p : Polynomial K => p.coeff 2) hS4sq
    rw [show S₄ ^ 2 = S₄ * S₄ by ring] at h2
    have hs2 : S₄.coeff 2 = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : S₄.natDegree < 2)
    rw [hW0c2] at h2
    simp [Polynomial.coeff_mul, hanti2] at h2
    rw [hs2] at h2
    linear_combination h2
  rw [hs1] at hc2
  have hne : (-216 : K) * α ^ 10 * lam ≠ 0 := by
    apply mul_ne_zero _ hlam
    apply mul_ne_zero _ (pow_ne_zero _ hα)
    norm_num
  exact hne (by rw [← hc2]; simp)

end E18end

/-! ### §9. E18 — Theorem 6.1 assembly (CONDITIONAL) -/

section E18asm

variable {K : Type*} [Field K] [CharZero K]

/-- E18 polygon discrepancy: the printed §6 lists transpose the middle
    vertex against Prop 4.4's lists (and against §6's own
    `ℓ_{1,0}(P) = x⁶y²`, `ℓ_{1,0}(Q) = x⁹y³`). The formalisation uses
    the Prop 4.4 lists. -/
theorem e18_polygon_discrepancy_P :
    ([(0, 0), (4, 0), (6, 2), (0, 14)] : List (ℕ × ℕ))
      ≠ [(0, 0), (4, 0), (2, 6), (0, 14)] := by decide

theorem e18_polygon_discrepancy_Q :
    ([(0, 0), (6, 0), (9, 3), (0, 21)] : List (ℕ × ℕ))
      ≠ [(0, 0), (6, 0), (3, 9), (0, 21)] := by decide

/-- E18 Theorem 6.1 core (CONDITIONAL): the §6 data cannot hold.
    Premises:
    * `hdm1mono` — the monomial form `dm1 = C α * X^k` (to be derived
      from `dm1⁶ ∣ X²⁷` via `dvd_prime_pow` (see `s6_dm1_monomial`);
    * `hprin` — the principal equation (KERNEL via
      `s6_principal_certificate` from the 9 displays);
    * `hsq` — the square identity (route: `square_identity_field`
      transferred through `RatFunc K`, or a Singular `lift` certificate;
      both pending VM work).
    The extra identities `hid2`, `hid3` and the final combination
    `e18_final_combination` are the route to `hsq`, not needed once
    `hsq` is given. The Prop 4.4 reduction (Leg B, E8) — that a
    counterexample yields this §6 data — is a further named premise of
    the full Theorem 6.1 and is NOT discharged here. -/
theorem s6_theorem61_core
    (d0 d1 dm1 : Polynomial K) (α lam : K)
    (hα : α ≠ 0) (hlam : lam ≠ 0)
    (hd0deg : d0.natDegree = 9) (hd1deg : d1.natDegree = 6)
    (hdm1mono : ∃ k : ℕ, dm1 = Polynomial.C α * Polynomial.X ^ k)
    (hprin : 9 * Polynomial.X ^ 9 * d1 * dm1 ^ 6 + Polynomial.X ^ 27
      + 27 * d0 * dm1 ^ 9 = 0)
    (hsq : (27 * Polynomial.C α ^ 9 * d0 - 2 * Polynomial.X ^ 9) ^ 2
      = 108 * Polynomial.C α ^ 10
        * (Polynomial.C α ^ 3 * Polynomial.X ^ 8
          - 2 * Polynomial.C lam * Polynomial.X ^ 10)) :
    False := by
  obtain ⟨k, hdm1k⟩ := hdm1mono
  rw [hdm1k] at hprin
  have hk : k = 2 := s6_k2 d0 d1 α hα k hd0deg hd1deg hprin
  subst hk
  exact s6_nonsquare d0 α lam hα hlam hsq

end E18asm

/-! ### §10. E21 — `D_k ∈ K[y]` by induction in `RatFunc K` -/

section E21rat

variable {K : Type*} [Field K] [CharZero K]

/-- `IsPolyRF z`: the rational function `z` is a polynomial in `y`
    (i.e. it lies in the image of `algebraMap (Polynomial K) (RatFunc K)`). -/
def IsPolyRF (z : RatFunc K) : Prop :=
  ∃ p : Polynomial K, algebraMap (Polynomial K) (RatFunc K) p = z

theorem IsPolyRF.zero : IsPolyRF (0 : RatFunc K) := ⟨0, by simp⟩

theorem IsPolyRF.one : IsPolyRF (1 : RatFunc K) := ⟨1, by simp⟩

theorem IsPolyRF.add {z w : RatFunc K} (hz : IsPolyRF z) (hw : IsPolyRF w) :
    IsPolyRF (z + w) := by
  obtain ⟨p, hp⟩ := hz
  obtain ⟨q, hq⟩ := hw
  exact ⟨p + q, by rw [map_add, hp, hq]⟩

theorem IsPolyRF.sub {z w : RatFunc K} (hz : IsPolyRF z) (hw : IsPolyRF w) :
    IsPolyRF (z - w) := by
  obtain ⟨p, hp⟩ := hz
  obtain ⟨q, hq⟩ := hw
  exact ⟨p - q, by rw [map_sub, hp, hq]⟩

theorem IsPolyRF.mul {z w : RatFunc K} (hz : IsPolyRF z) (hw : IsPolyRF w) :
    IsPolyRF (z * w) := by
  obtain ⟨p, hp⟩ := hz
  obtain ⟨q, hq⟩ := hw
  exact ⟨p * q, by rw [map_mul, hp, hq]⟩

theorem IsPolyRF.smul_const (c : K) {z : RatFunc K} (hz : IsPolyRF z) :
    IsPolyRF (RatFunc.C c * z) := by
  obtain ⟨p, hp⟩ := hz
  refine ⟨Polynomial.C c * p, ?_⟩
  rw [map_mul, hp, RatFunc.algebraMap_C]

theorem IsPolyRF.half {z : RatFunc K} (hz : IsPolyRF z) :
    IsPolyRF ((1 / 2 : RatFunc K) * z) := by
  have h : (1 / 2 : RatFunc K) = RatFunc.C (1 / 2 : K) := by
    rw [map_div₀, map_one, map_ofNat]
  rw [h]
  exact IsPolyRF.smul_const _ hz

theorem IsPolyRF.sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → RatFunc K}
    (hf : ∀ j ∈ s, IsPolyRF (f j)) : IsPolyRF (∑ j ∈ s, f j) := by
  induction s using Finset.induction with
  | empty => simpa using IsPolyRF.zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IsPolyRF.add (hf a (Finset.mem_insert_self a s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- E21 membership: if `D` satisfies the corrected recursion
    `D k = (1/2)·P(k+3)·y^{1-k} - (1/2)·Σ_{j=k+1}^{2} D j · D (k+3-j)`
    for `k ≤ 1` (cf. `e21_Dk_formula`), with `D 2` a polynomial and
    each `P(k+3)·y^{1-k}` a polynomial, then every `D k`, `k ≤ 2`, is
    a polynomial. Strong induction on `m = 2 - k`: each summand has
    both factors at indices strictly between `k` and `2`. The base
    case `D 2 ∈ K[y]` is the `y ∣ P₅` input from E19 (carried as the
    hypothesis `hD2`); the case `k = 3` is `e21_D3` (`D 3 = 1`). -/
theorem e21_membership {D P : ℤ → RatFunc K}
    (hD2 : IsPolyRF (D 2))
    (hrec : ∀ k : ℤ, k ≤ 1 → D k
      = (1 / 2 : RatFunc K) * (P (k + 3) * RatFunc.X ^ (1 - k))
        - (1 / 2 : RatFunc K)
          * ∑ j ∈ Finset.Icc (k + 1) 2, D j * D (k + 3 - j))
    (hP : ∀ k : ℤ, k ≤ 1 → IsPolyRF (P (k + 3) * RatFunc.X ^ (1 - k))) :
    ∀ k : ℤ, k ≤ 2 → IsPolyRF (D k) := by
  have key : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → IsPolyRF (D ((2 : ℤ) - (m : ℤ))) := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        simpa using hD2
    | succ n ih =>
        intro m hm
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · simpa using hD2
        · set k : ℤ := 2 - (m : ℤ) with hkdef
          have hkle : k ≤ 1 := by omega
          rw [hrec k hkle]
          apply IsPolyRF.sub
          · exact IsPolyRF.half (hP k hkle)
          · apply IsPolyRF.half
            apply IsPolyRF.sum
            intro j hj
            rw [Finset.mem_Icc] at hj
            obtain ⟨hjlo, hjhi⟩ := hj
            have hmle : (m : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast hm
            have hmj : IsPolyRF (D j) := by
              have h1 : IsPolyRF (D ((2 : ℤ) - (((2 - j).toNat : ℕ) : ℤ))) :=
                ih (2 - j).toNat (by
                  rw [Int.toNat_le]
                  omega)
              have hjj : (2 : ℤ) - (((2 - j).toNat : ℕ) : ℤ) = j := by
                rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ 2 - j)]
                ring
              rw [hjj] at h1
              exact h1
            have hmk : IsPolyRF (D (k + 3 - j)) := by
              have h1 : IsPolyRF (D ((2 : ℤ)
                  - (((2 - (k + 3 - j)).toNat : ℕ) : ℤ))) :=
                ih (2 - (k + 3 - j)).toNat (by
                  rw [Int.toNat_le]
                  omega)
              have hjj2 : (2 : ℤ) - (((2 - (k + 3 - j)).toNat : ℕ) : ℤ)
                  = k + 3 - j := by
                rw [Int.toNat_of_nonneg
                  (by omega : (0 : ℤ) ≤ 2 - (k + 3 - j))]
                ring
              rw [hjj2] at h1
              exact h1
            exact IsPolyRF.mul hmj hmk
  intro k hk
  have h1 : IsPolyRF (D ((2 : ℤ) - (((2 - k).toNat : ℕ) : ℤ))) :=
    key (2 - k).toNat (2 - k).toNat le_rfl
  have h2 : (2 : ℤ) - (((2 - k).toNat : ℕ) : ℤ) = k := by
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ 2 - k)]
    ring
  rw [h2] at h1
  exact h1

end E21rat

/-! ### §11. E18 — monomial form of `d₋₁` -/

section E18mono

variable {K : Type*} [Field K] [CharZero K]

/-- From the principal equation, `dm1⁶ ∣ X²⁷`:
    `X²⁷ = dm1⁶ · (-(9 X⁹ d₁ + 27 d₀ dm1³))`. -/
theorem s6_dm1_dvd (d0 d1 dm1 : Polynomial K)
    (hprin : 9 * Polynomial.X ^ 9 * d1 * dm1 ^ 6 + Polynomial.X ^ 27
      + 27 * d0 * dm1 ^ 9 = 0) :
    dm1 ^ 6 ∣ Polynomial.X ^ 27 := by
  use -(9 * Polynomial.X ^ 9 * d1 + 27 * d0 * dm1 ^ 3)
  linear_combination hprin

/-- Monomial form: if `dm1⁶ ∣ X²⁷` then `dm1 = C α · X^k` for some
    `α ≠ 0` (using that `X` is prime in `K[X]` and units are nonzero
    constants). Discharges the `hdm1mono` premise of
    `s6_theorem61_core`. -/
theorem s6_dm1_monomial {dm1 : Polynomial K}
    (hdvd : dm1 ^ 6 ∣ Polynomial.X ^ 27) :
    ∃ α : K, ∃ k : ℕ, α ≠ 0 ∧ dm1 = Polynomial.C α * Polynomial.X ^ k := by
  have h1 : dm1 ∣ Polynomial.X ^ 27 :=
    dvd_trans (dvd_pow_self dm1 (by norm_num : 6 ≠ 0)) hdvd
  obtain ⟨k, -, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X 27).mp h1
  obtain ⟨u, hu⟩ := hassoc
  have huinv : IsUnit (↑u⁻¹ : Polynomial K) := Units.isUnit u⁻¹
  obtain ⟨α, hαunit, hαC⟩ := Polynomial.isUnit_iff.mp huinv
  have hα : α ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero hαunit
  refine ⟨α, k, hα, ?_⟩
  have hdm1 : dm1 = Polynomial.X ^ k * (↑u⁻¹ : Polynomial K) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hdm1, mul_comm, ← hαC]

end E18mono

/-! ### §12. E18 — Theorem 6.1 assembly with `hdm1mono`/`hprin` discharged

`hdm1mono` (via `s6_dm1_dvd` + `s6_dm1_monomial`) and `hprin` (via
`s6_principal_eq` from the 9 displayed equations) are discharged here; the
only remaining mathematical premise is the square identity `hsq` (whose
derivation from the 9 equations + the extra identities + the final
combination is Singular-supported — `y⁹·T ∈ J`, GB-reduce 0 — but the
explicit `lift` coefficients did not complete, so it stays a premise).
The Prop 4.4 reduction (Leg B, E8) and the polygon-link check are NOT part
of this statement: this is the §6 endgame from the 9 equations onward. -/

section E18final

variable {K : Type*} [Field K] [CharZero K]

/-- Theorem 6.1 (§6 endgame, conditional on `hsq`): from the 9 displayed
    equations, `deg d₀ = 9`, `deg d₁ = 6`, `d₋₁ ≠ 0`, and the square
    identity, contradiction. -/
theorem s6_theorem61
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 : Polynomial K)
    (α lam : K) (hα : α ≠ 0) (hlam : lam ≠ 0)
    (hd0deg : d0.natDegree = 9) (hd1deg : d1.natDegree = 6)
    (hD21 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD22 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD23 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD24 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD25 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD27 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6
      + 2 * d0 * dm7 + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2
      + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4
      + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2
      + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4
      + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8 = 0)
    (hQ4x2 : 6 * dm10 + 6 * dm1 ^ 2 * dm2 + 6 * d0 * dm2 ^ 2
      + 12 * d0 * dm1 * dm3 + 12 * d1 * dm2 * dm3 + 6 * d0 ^ 2 * dm4
      + 12 * d1 * dm1 * dm4 + 12 * dm3 * dm4 + 12 * d0 * d1 * dm5
      + 12 * dm2 * dm5 + 6 * d1 ^ 2 * dm6 + 12 * dm1 * dm6 + 12 * d0 * dm7
      + 12 * d1 * dm8 + Polynomial.X ^ 9 = 0)
    (hdm1 : dm1 ≠ 0)
    (hsq : (27 * Polynomial.C α ^ 9 * d0 - 2 * Polynomial.X ^ 9) ^ 2
      = 108 * Polynomial.C α ^ 10
        * (Polynomial.C α ^ 3 * Polynomial.X ^ 8
          - 2 * Polynomial.C lam * Polynomial.X ^ 10)) :
    False := by
  have hprin := s6_principal_eq d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10
    hD21 hD22 hD23 hD24 hD25 hD27 hQ1 hQ2 hQ4x2 hdm1
  obtain ⟨α', k, hα', hdm1k⟩ := s6_dm1_monomial (s6_dm1_dvd d0 d1 dm1 hprin)
  rw [hdm1k] at hprin
  have hk : k = 2 := s6_k2 d0 d1 α' hα' k hd0deg hd1deg hprin
  subst hk
  exact s6_nonsquare d0 α lam hα hlam hsq

end E18final

/-! ## Axiom audit -/
#print axioms e19_v21_31
#print axioms e19_v21_b0_paper_wrong
#print axioms e19_v1m1_31
#print axioms e19_v21_yinv
#print axioms e19_v1m1_yinv
#print axioms e19_F_val
#print axioms e19_k_range
#print axioms ValAxioms.zero
#print axioms ValAxioms.inv
#print axioms ValAxioms.div
#print axioms ValAxioms.pow_nat
#print axioms ValAxioms.zpow
#print axioms ValAxioms.sum_le
#print axioms e19_bound_step_21
#print axioms e19_bound_step_1m1
#print axioms e19_recursion
#print axioms e19_finite_bounds
#print axioms e19_b0_corrected
#print axioms e23_bracket_coeff
#print axioms e23_verification
#print axioms e23_monomial_unique
#print axioms e23_ode_unique
#print axioms e23_ode_N0
#print axioms e20_Qtilde
#print axioms e20_Ctilde_sq_trunc
#print axioms e20_Ctilde_cu_trunc
#print axioms e20_assembly
#print axioms e21_DD_identity
#print axioms e21_Dk_formula
#print axioms e21_D3
#print axioms d2sq_eq_zero_of_gt
#print axioms d2sq_neg1
#print axioms d2sq_neg2
#print axioms d2sq_neg3
#print axioms d2sq_neg4
#print axioms d2sq_neg5
#print axioms d2sq_neg6
#print axioms d2sq_neg7
#print axioms d2sq_neg8
#print axioms d2sq_0
#print axioms d2sq_1
#print axioms d2sq_2
#print axioms d2sq_3
#print axioms d2sq_4
#print axioms d2sq_5
#print axioms d2sq_6
#print axioms d2sq_7
#print axioms d2sq_8
#print axioms d2sq_9
#print axioms d2sq_10
#print axioms d3cu_neg1
#print axioms d3cu_neg2
#print axioms d3cu_neg3
#print axioms d3cu_neg4
#print axioms s6_principal_certificate
#print axioms phi_shift_x2_paper
#print axioms phi_shift_x2_corrected
#print axioms e22_displays_from_vanishing
#print axioms s6_principal_eq
#print axioms poly_add_ne_zero_of_degree
#print axioms s6_k2
#print axioms e18_final_combination
#print axioms square_identity_field
#print axioms X_pow_dvd_of_sq
#print axioms s6_nonsquare
#print axioms e18_polygon_discrepancy_P
#print axioms e18_polygon_discrepancy_Q
#print axioms s6_theorem61_core
#print axioms IsPolyRF.zero
#print axioms IsPolyRF.one
#print axioms IsPolyRF.add
#print axioms IsPolyRF.sub
#print axioms IsPolyRF.mul
#print axioms IsPolyRF.smul_const
#print axioms IsPolyRF.half
#print axioms IsPolyRF.sum
#print axioms e21_membership
#print axioms s6_dm1_dvd
#print axioms s6_dm1_monomial
#print axioms s6_theorem61
