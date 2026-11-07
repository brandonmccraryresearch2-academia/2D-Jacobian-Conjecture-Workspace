/-
  GGHV Laurent-series library fragment — minimal, programme-level blocker.
  Paper: arXiv:2204.14178v1, TeX ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.
  Leg C: ~/workspace/research/tooling/phase4_legC/gghv_full_s5_2026-11-06.lean (E11).
  Leg D: ~/workspace/research/tooling/phase4_legD/gghv_full_s6_2026-11-06.lean (E19/E20/E23).
  Inventory: ~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/gghv_statement_inventory.md.

  CLAIM: see the per-section verdicts below. STATUS: full file verified 2026-11-06
  ~23:55 CST on lean-build-3 (Lean 4.34.0 / Lake 5.0.0): FULL_RC=0, 0 errors,
  ~10 s; full axioms audit (87 theorems): all on the permitted triple
  [propext, Classical.choice, Quot.sound] or a subset, sorryAx count 0.
  Toolchain: Lean 4.34.0, Mathlib v4.34.0 (on lean-build-3). No `sorry`, no `axiom`.

  Ambient types (verified against the TeX, NOT the task's shorthand):
  - §5 E11: C, F ∈ K[y, C₃⁻¹]((x⁻¹)), C₃ = y⁸(y+1). Coefficient ring: localisation at C₃.
  - §6 E19: C, F ∈ K[y,y⁻¹]((x⁻¹)). Coefficient ring: Laurent polynomials in y.
  - Series variable in Mathlib: LaurentSeries A = A⟦ℤ⟧ (HahnSeries), variable t = x⁻¹,
    so C = Σ_{n≤3} Cₙ xⁿ is the series with t-support bounded below by -3.
    x := single (-1) 1, y := C (T 1), t := single 1 1.

  Mathlib API record (Lean 4.34.0, probed 2026-11-06 on lean-build-3):
  - EXISTS: LaurentSeries R := R⟦ℤ⟧ (HahnSeries); HahnSeries.coeff, coeff_mul
    (support-restricted antidiagonal), single, C, ext, order, orderTop, order_mul,
    order_neg, order_single, order_C, addVal (AddValuation, needs IsDomain R);
    LaurentSeries.derivative / hasseDeriv with hasseDeriv_coeff;
    ofPowerSeries, coeff_coe_powerSeries; PowerSeries.mk, coeff_mk, coeff_mul
    (ℕ antidiagonal), ext, isUnit_iff_constantCoeff, invOfUnit;
    LaurentPolynomial: T, isUnit_T, degree : WithBot ℤ, degree_T, degree_C,
    degree_C_mul_T; RatFunc.intDegree with intDegree_mul/add_le/zero/one/X/neg/inv/C;
    Field (LaurentSeries (RatFunc K)) instance.
  - MISSING: LaurentPolynomial.degree_mul (no such lemma); LaurentSeries.X;
    PowerSeries.isUnit_iff (name is isUnit_iff_constantCoeff);
    RatFunc.derivative; LaurentPolynomial.derivative; Leibniz rule for
    hasseDeriv/derivative on HahnSeries; any (ρ,σ)-valuation; any two-variable
    Laurent series. The fragment below builds only what the assembly needs on top
    of the existing API; it does NOT rebuild the HahnSeries ring.

  Per-section verdicts (HLRE v5; KERNEL = kernel-verified on the permitted triple
  [propext, Classical.choice, Quot.sound] or a subset; CONDITIONAL = proved from the
  named premises; BLOCKED = not formalised, blocker stated):
  - §1 (ValAxioms diagnosis): KERNEL. Leg D's ValAxioms admits ONLY w ≡ 0
    (valAxioms_forces_zero); its `add` axiom is inconsistent with any valuation
    taking a negative value (valAxioms_nonneg). Hence Leg D's e19_bound_step_21,
    e19_bound_step_1m1, e19_finite_bounds can NEVER be instantiated with the
    intended v_{2,1} / v_{1,-1}. This is a genuine defect in Leg D's abstract
    framework, not in its proofs (the implications are kernel-proved, but vacuous
    for the intended application).
  - §2 (corrected axioms + bound steps): KERNEL (abstract). ValCore (nonzero guards
    on mul, sum≠0 guard on add, w 0 = 0 as a field) + derived inv/div/pow/sum_le
    + the (b_k)/(c_k) bound steps and the finite-bounds induction, all proved
    from ValCore alone. These REPLACE Leg D's ValAxioms versions for assembly.
  - §3a (w21 on RatFunc K): KERNEL. RatFunc.intDegree satisfies ValCore, with
    w(y) = 1, w(2y) = 1. This instantiates the (2,1) side at coefficient level.
  - §3b (LP valuations): KERNEL. Max/min y-degree on LaurentPolynomial K satisfy
    ValCore (`valCore_lpMaxDeg`, `valCore_lpMinDeg`); the one-term product argument
    is via `AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd`.
  - §4 (series square-root construction): KERNEL. `exists_sqrt_series` (generic
    power-series square root) + `e19_sqrt_s6` + `e19_existence_bounds_s6` (§6
    existence with the (b_k)/(c_k) bounds, from `valcore_finite_bounds` at the two
    kernel LP valuations with the unit d = (2y)⁻¹).
  - §5 (bracket): PARTIAL — KERNEL: monomial bracket (`bracket_mono`), E23 instance
    (`e23_instance`), bracket additivity; CONDITIONAL: series reduction
    (`e23_series_reduction`) on the bracket-degree bound `hdeg` (needs the Leibniz
    rule for `LaurentSeries.derivative`, absent from Mathlib 4.34.0).
  - §6 (F-construction): PARTIAL — KERNEL: `v10` (the (1,0)-valuation `-(order)`)
    satisfies `ValCore` (`valCore_v10`); `v10_of_coeff` (v10 C = 3 from the leading
    coefficient); `v10_C_s6`. CONDITIONAL: `exists_F` on the named bundle
    `GGV1Inputs` (cancel + leading at coefficient level = the [GGV3] §1 α-choice
    + [GGV1] Prop 1.13/2.1 content); the bracket step `[C^k, C²] = 0` is a named
    hypothesis `bracket_pow_C` (NOT proved: needs the Leibniz rule for
    `LaurentSeries.derivative`, absent from Mathlib 4.34.0).
  - §7 (tilde series): KERNEL (modulo the `Ptcoef` data). `exists_tilde` (Ct² = Pt,
    Ct * Cti = 1, Qtilde = Ct³ + lam' * Cti + Ft, Ct.coeff (-3) = C3, with the
    `recDiag` coefficient data). The paper's sharper claim (Ft has v10 = -4,
    lam' = lam - α₁²/3 + …) is NOT proved — Ft is defined as the difference.
  - §8 (assembly interface): KERNEL / CONDITIONAL as labelled per theorem.
    `laurent_series_discharge_s6` (KERNEL: E19 existence + bounds + v10 C = 3 +
    leading term x³y); `tilde_discharge` (KERNEL modulo the `Ptcoef`
    construction, via `tilde_Ptcoef`); `bracket_reduction_discharge`
    (CONDITIONAL on `hdeg`, as in `e23_series_reduction`); `f_discharge`
    (CONDITIONAL on `GGV1Inputs`); `isUnit_of_coeff` (KERNEL: a series is a
    unit iff its leading coefficient is a unit, via `HahnSeries.isUnit_iff`);
    `exists_F_lp` + `f_discharge_lp_s6` (CONDITIONAL on `GGV1InputsLp` and the
    unit `u` with `↑u = C`).

  Paper slips NOT copied (verified by the legs, restated here): §5 recursion sign
  error (TeX ~1462–1465, corrected form used); φ-shift t = D₂/3, not D₂;
  valuation product-vs-sum typo (bound is additive); E21/E14 D_k formula omits
  1/2 on the sum; §6 (b₀) v_{2,1}(3,1) = 7, not 6.
-/
import Mathlib

open Finset HahnSeries LaurentSeries LaurentPolynomial PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-! ## §1. Leg D's `ValAxioms` admits only the zero valuation (KERNEL diagnosis).

  The structure below is a VERBATIM copy of Leg D's `ValAxioms`
  (gghv_full_s6_2026-11-06.lean, §1): the same fields, the same types.
  The two lemmas show it is uninstantiable for the intended valuations. -/

/-- Verbatim copy of Leg D's `ValAxioms` (field `F`, `w : F → ℤ`). -/
structure ValAxiomsOrig (F : Type*) [Field F] (w : F → ℤ) : Prop where
  mul : ∀ a b, w (a * b) = w a + w b
  add : ∀ a b, w (a + b) ≤ max (w a) (w b)
  neg : ∀ a, w (-a) = w a
  one : w 1 = 0
  two : w (2 : F) = 0

namespace ValAxiomsOrig

variable {F : Type*} [Field F] {w : F → ℤ}

/-- The `mul` axiom alone forces `w ≡ 0`: take `a = 0`. -/
theorem forces_zero (hw : ValAxiomsOrig F w) (a : F) : w a = 0 := by
  have h := hw.mul 0 a
  simp only [zero_mul] at h
  omega

/-- In particular `w 0 = 0`. -/
theorem zero (hw : ValAxiomsOrig F w) : w 0 = 0 := hw.forces_zero 0

/-- The `add` axiom forces `w ≥ 0` everywhere (with `w 0 = 0` and `neg`):
    `0 = w (a + -a) ≤ max (w a) (w (-a)) = w a`. So no valuation taking a
    negative value (e.g. `v_{2,1}(y⁻¹) = -1`, `v_{1,-1}(y) = -1`) can satisfy
    `ValAxiomsOrig`. Together with `forces_zero` this is a second, independent
    obstruction. -/
theorem nonneg (hw : ValAxiomsOrig F w) (a : F) : 0 ≤ w a := by
  have h := hw.add a (-a)
  rw [add_neg_cancel, hw.zero, hw.neg] at h
  omega

/-- Consequence: `v_{2,1}` with `w x = 2` (or any `w a ≠ 0`) is impossible. -/
theorem no_nontrivial (hw : ValAxiomsOrig F w) {a : F} (ha : w a ≠ 0) : False :=
  ha (hw.forces_zero a)

end ValAxiomsOrig

/-! ## §2. Corrected valuation axioms (`ValCore`) + bound steps (KERNEL, abstract).

  Fixes, relative to `ValAxiomsOrig`: `mul` only for nonzero factors; `add`
  only when the sum is nonzero; `w 0 = 0` as a separate field. The bound steps
  below are the corrected versions of Leg D's `e19_bound_step_21`,
  `e19_bound_step_1m1` and `e19_finite_bounds`: same conclusions, but the
  recursion is stated with an explicit unit `d : Rˣ` (the element `(2y)⁻¹`,
  as a unit) instead of field division, so the statements work over any
  commutative ring in which `2y` is a unit — in particular over
  `LaurentPolynomial K` (where `y = T 1` is a unit) and over any field.
  The two valuations in `finite_bounds` share the SAME unit `d` (hypothesis
  `hd_eq`); the two `w`-values of `d` differ (`-1` resp. `+1`), as they must:
  `w21 (2y) = 1`, `w1m1 (2y) = -1`. -/

/-- Corrected ℤ-valued valuation axioms on a commutative ring. -/
structure ValCore (R : Type*) [CommRing R] (w : R → ℤ) : Prop where
  zero : w 0 = 0
  mul : ∀ a b, a ≠ 0 → b ≠ 0 → w (a * b) = w a + w b
  add : ∀ a b, a + b ≠ 0 → w (a + b) ≤ max (w a) (w b)
  neg : ∀ a, w (-a) = w a
  one : w 1 = 0
  two : w (2 : R) = 0

/-- `a ^ n ≠ 0` for `a ≠ 0` in a domain (Mathlib's `pow_ne_zero` in 4.34
    resolves to a version requiring `IsReduced`; this induction avoids it). -/
theorem pow_ne_zero_of_ne {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (a : R) (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_ne_zero
  | succ n ih => rw [pow_succ]; exact mul_ne_zero ih ha

namespace ValCore

variable {R : Type*} [CommRing R] [Nontrivial R] {w : R → ℤ}

theorem inv_unit (hw : ValCore R w) (u : Rˣ) : w ((u⁻¹ : Rˣ) : R) = -w (u : R) := by
  have hu : (u : R) ≠ 0 := Units.ne_zero u
  have hui : ((u⁻¹ : Rˣ) : R) ≠ 0 := Units.ne_zero u⁻¹
  have h := hw.mul (u : R) ((u⁻¹ : Rˣ) : R) hu hui
  have e : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← Units.val_mul]; simp
  rw [e, hw.one] at h
  omega

theorem pow (hw : ValCore R w) [NoZeroDivisors R] (a : R) (n : ℕ) (ha : a ≠ 0) :
    w (a ^ n) = (n : ℤ) * w a := by
  induction n with
  | zero => simp [hw.one]
  | succ n ih =>
    rw [pow_succ, hw.mul _ _ (pow_ne_zero_of_ne a ha n) ha, ih]
    push_cast
    ring

/-- A finite sum is bounded by the common bound of its terms (for `B ≥ 0`).
    The `add` axiom's sum≠0 side condition is discharged by case splits
    (a vanishing partial sum has `w = 0 ≤ B`). -/
theorem sum_le (hw : ValCore R w) {s : Finset ℤ} {f : ℤ → R} {B : ℤ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  induction s using Finset.induction_on with
  | empty => simp [hw.zero, hB]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      by_cases h0 : f a + ∑ i ∈ s, f i = 0
      · rw [h0, hw.zero]; exact hB
      · exact le_trans (hw.add _ _ h0) (max_le h1 h2)

end ValCore

section ValCoreField

variable {F : Type*} [Field F] {w : F → ℤ}

theorem ValCore.inv (hw : ValCore F w) {a : F} (ha : a ≠ 0) : w a⁻¹ = -w a := by
  have h := hw.mul a a⁻¹ ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, hw.one] at h
  omega

theorem ValCore.div (hw : ValCore F w) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    w (a / b) = w a - w b := by
  rw [div_eq_mul_inv, hw.mul _ _ ha (inv_ne_zero hb), hw.inv hb, sub_eq_add_neg]

theorem ValCore.zpow (hw : ValCore F w) {a : F} (ha : a ≠ 0) (n : ℤ) :
    w (a ^ n) = n * w a := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hw.pow a n ha
  | negSucc n =>
      rw [zpow_negSucc, hw.inv (pow_ne_zero _ ha), hw.pow a (n + 1) ha]
      have e : (Int.negSucc n : ℤ) = -((n : ℤ) + 1) := rfl
      rw [e]; push_cast; ring

end ValCoreField

/-! #### Corrected `(b_k)` / `(c_k)` bound steps and finite bounds.

  These are the corrected forms of Leg D's `e19_bound_step_21`,
  `e19_bound_step_1m1` and `e19_finite_bounds`. Differences from Leg D:
  (i) `ValCore` in place of the inconsistent `ValAxiomsOrig`;
  (ii) the recursion step is stated with multiplication by a unit `d`
  (the element `(2y)⁻¹`) instead of division by `2y`, so the lemmas apply
  over a ring as well as over a field;
  (iii) no nonzero hypotheses on the `C`-coefficients are needed: a vanishing
  factor makes the product vanish, and `w 0 = 0` is below the (nonneg) bounds.
  The `2`-unit hypothesis `h2 : (2 : R) ≠ 0` is used only to know `d ≠ 0`
  (via `Units.ne_zero`); `CharZero` is NOT assumed. -/

section BoundSteps

variable {R : Type*} [CommRing R] [Nontrivial R] {w21 w1m1 : R → ℤ}

/-- Corrected `(b_k)` step (Leg D `e19_bound_step_21`): from
    `w21 (C_{3-j}) ≤ 1 + 2j` for `1 ≤ j ≤ k-1` and `w21 (P_{6-k}) ≤ 2 + 2k`,
    with `w21 y = 1` and `w21 d = -1` (so `d` plays the role of `(2y)⁻¹`),
    the recursion gives `w21 ((P_{6-k} - Σ…) * d) ≤ 1 + 2k`. -/
theorem valcore_bound_step_21 (hw21 : ValCore R w21)
    {y : R} (_hy : w21 y = 1)
    (d : Rˣ) (hd : w21 (d : R) = -1)
    {k : ℤ} (hk : 1 ≤ k) (C P : ℤ → R)
    (hC : ∀ j : ℤ, 1 ≤ j → j ≤ k - 1 → w21 (C (3 - j)) ≤ 1 + 2 * j)
    (hP : w21 (P (6 - k)) ≤ 2 + 2 * k) :
    w21 ((P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) * (d : R))
      ≤ 1 + 2 * k := by
  have hd0 : (d : R) ≠ 0 := Units.ne_zero d
  have hterm : ∀ j ∈ Finset.Icc 1 (k - 1),
      w21 (C (3 - j) * C (3 - k + j)) ≤ 2 + 2 * k := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    by_cases h1 : C (3 - j) = 0
    · rw [h1, zero_mul, hw21.zero]; omega
    by_cases h2 : C (3 - k + j) = 0
    · rw [h2, mul_zero, hw21.zero]; omega
    · rw [hw21.mul _ _ h1 h2]
      have hb1 := hC j hj.1 hj.2
      have hb2 := hC (k - j) (by omega) (by omega)
      have heq : (3 : ℤ) - k + j = 3 - (k - j) := by ring
      rw [← heq] at hb2
      omega
  have hS : w21 (∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) ≤ 2 + 2 * k :=
    hw21.sum_le (by omega) hterm
  by_cases hPS : P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j) = 0
  · rw [hPS, zero_mul, hw21.zero]; omega
  · rw [hw21.mul _ _ hPS hd0, hd]
    have hPSb : w21 (P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j))
        ≤ 2 + 2 * k := by
      have hne : P (6 - k)
          + (-∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) ≠ 0 := by
        rwa [← sub_eq_add_neg]
      have hsub := hw21.add (P (6 - k))
        (-∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) hne
      rw [hw21.neg, ← sub_eq_add_neg] at hsub
      exact le_trans hsub (max_le hP hS)
    omega

/-- Corrected `(c_k)` step (Leg D `e19_bound_step_1m1`): from
    `w1m1 (C_{3-j}) ≤ j - 1` for `1 ≤ j ≤ k-1` and `w1m1 (P_{6-k}) ≤ k - 2`,
    with `w1m1 y = -1` and `w1m1 d = 1` (so `d` plays the role of `(2y)⁻¹`),
    the recursion gives `w1m1 ((P_{6-k} - Σ…) * d) ≤ k - 1`. -/
theorem valcore_bound_step_1m1 (hw1m1 : ValCore R w1m1)
    {y : R} (_hy : w1m1 y = -1)
    (d : Rˣ) (hd : w1m1 (d : R) = 1)
    {k : ℤ} (hk : 1 ≤ k) (C P : ℤ → R)
    (hC : ∀ j : ℤ, 1 ≤ j → j ≤ k - 1 → w1m1 (C (3 - j)) ≤ j - 1)
    (hP : w1m1 (P (6 - k)) ≤ k - 2) :
    w1m1 ((P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) * (d : R))
      ≤ k - 1 := by
  have hd0 : (d : R) ≠ 0 := Units.ne_zero d
  by_cases hk1 : k = 1
  · subst hk1
    have hempty : Finset.Icc (1 : ℤ) (1 - 1) = ∅ :=
      Finset.Icc_eq_empty (by norm_num)
    rw [hempty, Finset.sum_empty, sub_zero]
    by_cases hP0 : P (6 - 1) = 0
    · rw [hP0, zero_mul, hw1m1.zero]; norm_num
    · rw [hw1m1.mul _ _ hP0 hd0, hd]; omega
  · have hk2 : 2 ≤ k := by omega
    have hterm : ∀ j ∈ Finset.Icc 1 (k - 1),
        w1m1 (C (3 - j) * C (3 - k + j)) ≤ k - 2 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      by_cases h1 : C (3 - j) = 0
      · rw [h1, zero_mul, hw1m1.zero]; omega
      by_cases h2 : C (3 - k + j) = 0
      · rw [h2, mul_zero, hw1m1.zero]; omega
      · rw [hw1m1.mul _ _ h1 h2]
        have hb1 := hC j hj.1 hj.2
        have hb2 := hC (k - j) (by omega) (by omega)
        have heq : (3 : ℤ) - k + j = 3 - (k - j) := by ring
        rw [← heq] at hb2
        omega
    have hS : w1m1 (∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) ≤ k - 2 :=
      hw1m1.sum_le (by omega) hterm
    by_cases hPS : P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j) = 0
    · rw [hPS, zero_mul, hw1m1.zero]; omega
    · rw [hw1m1.mul _ _ hPS hd0, hd]
      have hPSb : w1m1 (P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j))
          ≤ k - 2 := by
        have hne : P (6 - k)
            + (-∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) ≠ 0 := by
          rwa [← sub_eq_add_neg]
        have hsub := hw1m1.add (P (6 - k))
          (-∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) hne
        rw [hw1m1.neg, ← sub_eq_add_neg] at hsub
        exact le_trans hsub (max_le hP hS)
      omega

/-- Corrected finite-bounds induction (Leg D `e19_finite_bounds`): with
    `C 3 = y`, the recursion (with unit `d21`; `d1m1` the same ring element)
    and the `P`-bounds, `w21 (C_{3-n}) ≤ 1 + 2n` and `w1m1 (C_{3-n}) ≤ n - 1`
    for every `n`. The `x`-hypotheses of Leg D's statement are dropped: its
    proof never uses them (only the `y`-values and the recursion are used). -/
theorem valcore_finite_bounds (hw21 : ValCore R w21) (hw1m1 : ValCore R w1m1)
    {y : R} (hy21 : w21 y = 1) (hy1m1 : w1m1 y = -1)
    (d21 d1m1 : Rˣ) (hd21 : w21 (d21 : R) = -1) (hd1m1 : w1m1 (d1m1 : R) = 1)
    (hd_eq : (d21 : R) = (d1m1 : R))
    (C P : ℤ → R)
    (hC3 : C 3 = y)
    (hrec : ∀ k : ℤ, 1 ≤ k → C (3 - k) =
      (P (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), C (3 - j) * C (3 - k + j)) * (d21 : R))
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
          · exact valcore_bound_step_21 hw21 hy21 d21 hd21 (k := (n : ℤ) + 1)
              (by omega) C P hC21 (hP21 _ (by omega))
          · rw [hd_eq]
            exact valcore_bound_step_1m1 hw1m1 hy1m1 d1m1 hd1m1 (k := (n : ℤ) + 1)
              (by omega) C P hC1m1 (hP1m1 _ (by omega))
  intro n
  exact key n n le_rfl

/-- The `(b₀)` bound in corrected form: `w21 (x³ * y) = 7` from `w21 x = 2`,
    `w21 y = 1` (Leg D `e19_b0_corrected`, with the paper's 6 corrected to 7). -/
theorem valcore_b0_21 [NoZeroDivisors R] (hw21 : ValCore R w21) {x y : R} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx21 : w21 x = 2) (hy21 : w21 y = 1) :
    w21 (x ^ (3 : ℕ) * y) = 7 := by
  rw [hw21.mul _ _ (pow_ne_zero_of_ne x hx0 3) hy0, hw21.pow x 3 hx0, hx21, hy21]
  norm_num

end BoundSteps

/-! ## §3a. The `(2,1)`-valuation at coefficient level: `RatFunc.intDegree` (KERNEL).

  `w21Rat r := r.intDegree` satisfies `ValCore` on the field `RatFunc K`
  (all API exists in Mathlib: `intDegree_mul`, `intDegree_add_le`,
  `intDegree_zero/one/neg/C`). It is the max-y-degree valuation: for a
  Laurent polynomial `r`, `intDegree r` is its highest `y`-exponent, so
  `w21Rat` restricted to `K[y,y⁻¹]` is exactly the coefficient valuation
  `v_{2,1}` of the legs (`w (C_{3-j})` in `valcore_bound_step_21`).
  Values: `w21Rat y = 1`, `w21Rat (2y) = 1`, hence the unit
  `d := (Units.mk0 (2y) _)⁻¹` has `w21Rat d = -1`, as `valcore_finite_bounds`
  requires. -/

/-- `RatFunc.intDegree` is a `ValCore` valuation. -/
theorem valCore_ratFunc_intDegree :
    ValCore (RatFunc K) (fun r => r.intDegree) where
  zero := RatFunc.intDegree_zero
  mul := fun a b ha hb => RatFunc.intDegree_mul ha hb
  add := by
    intro a b hab
    show (a + b).intDegree ≤ max a.intDegree b.intDegree
    by_cases hb : b = 0
    · rw [hb, add_zero, RatFunc.intDegree_zero]
      exact le_max_left _ _
    · exact RatFunc.intDegree_add_le hb hab
  neg := fun a => RatFunc.intDegree_neg a
  one := RatFunc.intDegree_one
  two := by
    show (2 : RatFunc K).intDegree = 0
    have h : (2 : RatFunc K) = RatFunc.C 2 := (map_ofNat _ _).symm
    rw [h, RatFunc.intDegree_C]

/-- Values used by the finite-bounds instantiation. -/
theorem w21Rat_y : (RatFunc.X : RatFunc K).intDegree = 1 := RatFunc.intDegree_X

theorem w21Rat_two_mul_y :
    ((2 : RatFunc K) * RatFunc.X).intDegree = 1 := by
  have h2 : (2 : RatFunc K).intDegree = 0 := by
    have h : (2 : RatFunc K) = RatFunc.C 2 := (map_ofNat _ _).symm
    rw [h, RatFunc.intDegree_C]
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := by
    intro hX0
    have h1 := RatFunc.intDegree_X (K := K)
    rw [hX0, RatFunc.intDegree_zero] at h1
    omega
  rw [valCore_ratFunc_intDegree.mul _ _ (by norm_num : (2 : RatFunc K) ≠ 0) hX, h2,
    RatFunc.intDegree_X]
  norm_num

/-! ### §3b. Max/min y-degree valuations on `LaurentPolynomial K`

The (2,1) valuation on §6 coefficients is max y-degree; the (1,-1) valuation is
(min y-degree) with a sign flip. Both are proved here as `ValCore` instances, by
a one-term (unique-pair) argument for multiplication and a support argument for
addition. Mathlib 4.34.0 has `LaurentPolynomial.degree` but no `degree_mul`, so
both degree laws are proved from `AddMonoidAlgebra.coeff_mul` +
`coeff_mul_add_of_uniqueAdd`. -/

/-- Max y-degree of a Laurent polynomial, as an integer (0 on the zero polynomial). -/
noncomputable def lpMaxDeg (f : LaurentPolynomial K) : ℤ :=
  if h : f.coeff.support.Nonempty then f.coeff.support.max' h else 0

/-- Minus min y-degree of a Laurent polynomial, as an integer (0 on zero). -/
noncomputable def lpMinDeg (f : LaurentPolynomial K) : ℤ :=
  if h : f.coeff.support.Nonempty then -(f.coeff.support.min' h) else 0

theorem lp_support_nonempty {f : LaurentPolynomial K} (hf : f ≠ 0) :
    f.coeff.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, Finsupp.support_eq_empty]
  intro h
  exact hf (AddMonoidAlgebra.coeffEquiv.injective (by simpa using h))

theorem lp_coeff_add (f g : LaurentPolynomial K) :
    (f + g).coeff = f.coeff + g.coeff := rfl

theorem lp_coeff_neg (f : LaurentPolynomial K) : (-f).coeff = -f.coeff := rfl

theorem lpMaxDeg_zero : lpMaxDeg (0 : LaurentPolynomial K) = 0 := by
  unfold lpMaxDeg
  rw [dif_neg (by rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty]; rfl)]

theorem lpMinDeg_zero : lpMinDeg (0 : LaurentPolynomial K) = 0 := by
  unfold lpMinDeg
  rw [dif_neg (by rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty]; rfl)]

/-- Bridge: on nonzero `f`, `lpMaxDeg f` is the coercion of `f.degree`. -/
theorem lpMaxDeg_eq_degree {f : LaurentPolynomial K} (hf : f ≠ 0) :
    (lpMaxDeg f : WithBot ℤ) = f.degree := by
  unfold lpMaxDeg
  rw [dif_pos (lp_support_nonempty hf), Finset.coe_max']; rfl

theorem lpMaxDeg_T (n : ℤ) : lpMaxDeg (T n : LaurentPolynomial K) = n := by
  have hne : (T n : LaurentPolynomial K) ≠ 0 := (isUnit_T n).ne_zero
  have h := lpMaxDeg_eq_degree hne
  rw [degree_T] at h
  exact WithBot.coe_eq_coe.mp h

theorem lp_support_C {a : K} (ha : a ≠ 0) :
    (C a : LaurentPolynomial K).coeff.support = {0} := by
  have h1 : (C a : LaurentPolynomial K) = AddMonoidAlgebra.single 0 a := by
    rw [single_eq_C_mul_T a 0, T_zero, mul_one]
  rw [h1, AddMonoidAlgebra.coeff_single]
  exact Finsupp.support_single 0 ha

theorem lpMaxDeg_C {a : K} (ha : a ≠ 0) : lpMaxDeg (C a : LaurentPolynomial K) = 0 := by
  unfold lpMaxDeg
  rw [lp_support_C ha, dif_pos (Finset.singleton_nonempty 0)]
  exact Finset.max'_singleton 0

theorem lp_support_T (n : ℤ) :
    (T n : LaurentPolynomial K).coeff.support = {n} := by
  have h1 : (T n : LaurentPolynomial K) = AddMonoidAlgebra.single n 1 := by
    rw [single_eq_C_mul_T 1 n, map_one, one_mul]
  rw [h1, AddMonoidAlgebra.coeff_single]
  exact Finsupp.support_single n one_ne_zero

theorem lpMinDeg_T (n : ℤ) : lpMinDeg (T n : LaurentPolynomial K) = -n := by
  unfold lpMinDeg
  rw [lp_support_T, dif_pos (Finset.singleton_nonempty n)]
  exact congrArg Neg.neg (Finset.min'_singleton n)

theorem lpMinDeg_C {a : K} (ha : a ≠ 0) : lpMinDeg (C a : LaurentPolynomial K) = 0 := by
  unfold lpMinDeg
  rw [lp_support_C ha, dif_pos (Finset.singleton_nonempty 0), Finset.min'_singleton, neg_zero]

/-- One-term multiplication law for max-degree (unique top pair). -/
theorem lpMaxDeg_mul {f g : LaurentPolynomial K} (hf : f ≠ 0) (hg : g ≠ 0) :
    lpMaxDeg (f * g) = lpMaxDeg f + lpMaxDeg g := by
  have hf' := lp_support_nonempty hf
  have hg' := lp_support_nonempty hg
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hfg' := lp_support_nonempty hfg
  have huniq : UniqueAdd f.coeff.support g.coeff.support
      (f.coeff.support.max' hf') (g.coeff.support.max' hg') := by
    intro a' b' ha' hb' h
    have ha : a' ≤ f.coeff.support.max' hf' := Finset.le_max' _ _ ha'
    have hb : b' ≤ g.coeff.support.max' hg' := Finset.le_max' _ _ hb'
    constructor <;> omega
  have htop : (f * g).coeff (f.coeff.support.max' hf' + g.coeff.support.max' hg')
      = f.coeff (f.coeff.support.max' hf') * g.coeff (g.coeff.support.max' hg') :=
    AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq
  have htop_ne : f.coeff (f.coeff.support.max' hf') *
      g.coeff (g.coeff.support.max' hg') ≠ 0 := by
    apply mul_ne_zero
    · exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
    · exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
  have hvanish : ∀ k : ℤ, (f * g).coeff k ≠ 0 →
      k ≤ f.coeff.support.max' hf' + g.coeff.support.max' hg' := by
    intro k hk
    rw [AddMonoidAlgebra.coeff_mul] at hk
    simp only [Finsupp.sum] at hk
    by_contra hgt
    push_neg at hgt
    apply hk
    refine Finset.sum_eq_zero fun m₁ hm₁ => Finset.sum_eq_zero fun m₂ hm₂ => ?_
    rw [if_neg]
    intro hbad
    have h1 : m₁ ≤ f.coeff.support.max' hf' := Finset.le_max' _ _ hm₁
    have h2 : m₂ ≤ g.coeff.support.max' hg' := Finset.le_max' _ _ hm₂
    omega
  unfold lpMaxDeg
  rw [dif_pos hfg', dif_pos hf', dif_pos hg']
  apply le_antisymm
  · exact Finset.max'_le _ hfg' _
      (fun k hk => hvanish k (Finsupp.mem_support_iff.mp hk))
  · exact Finset.le_max' _ _
      (Finsupp.mem_support_iff.mpr (by rw [htop]; exact htop_ne))

/-- One-term multiplication law for min-degree (unique bottom pair). -/
theorem lpMinDeg_mul {f g : LaurentPolynomial K} (hf : f ≠ 0) (hg : g ≠ 0) :
    lpMinDeg (f * g) = lpMinDeg f + lpMinDeg g := by
  have hf' := lp_support_nonempty hf
  have hg' := lp_support_nonempty hg
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hfg' := lp_support_nonempty hfg
  have huniq : UniqueAdd f.coeff.support g.coeff.support
      (f.coeff.support.min' hf') (g.coeff.support.min' hg') := by
    intro a' b' ha' hb' h
    have ha : f.coeff.support.min' hf' ≤ a' := Finset.min'_le _ _ ha'
    have hb : g.coeff.support.min' hg' ≤ b' := Finset.min'_le _ _ hb'
    constructor <;> omega
  have htop : (f * g).coeff (f.coeff.support.min' hf' + g.coeff.support.min' hg')
      = f.coeff (f.coeff.support.min' hf') * g.coeff (g.coeff.support.min' hg') :=
    AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq
  have htop_ne : f.coeff (f.coeff.support.min' hf') *
      g.coeff (g.coeff.support.min' hg') ≠ 0 := by
    apply mul_ne_zero
    · exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    · exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  have hvanish : ∀ k : ℤ, (f * g).coeff k ≠ 0 →
      f.coeff.support.min' hf' + g.coeff.support.min' hg' ≤ k := by
    intro k hk
    rw [AddMonoidAlgebra.coeff_mul] at hk
    simp only [Finsupp.sum] at hk
    by_contra hlt
    push_neg at hlt
    apply hk
    refine Finset.sum_eq_zero fun m₁ hm₁ => Finset.sum_eq_zero fun m₂ hm₂ => ?_
    rw [if_neg]
    intro hbad
    have h1 : f.coeff.support.min' hf' ≤ m₁ := Finset.min'_le _ _ hm₁
    have h2 : g.coeff.support.min' hg' ≤ m₂ := Finset.min'_le _ _ hm₂
    omega
  have hmin : (f * g).coeff.support.min' hfg'
      = f.coeff.support.min' hf' + g.coeff.support.min' hg' := by
    apply le_antisymm
    · exact Finset.min'_le _ _
        (Finsupp.mem_support_iff.mpr (by rw [htop]; exact htop_ne))
    · exact Finset.le_min' _ _ _
        (fun k hk => hvanish k (Finsupp.mem_support_iff.mp hk))
  unfold lpMinDeg
  rw [dif_pos hfg', dif_pos hf', dif_pos hg', hmin]
  ring

theorem lpMaxDeg_add_le {f g : LaurentPolynomial K} (hfg : f + g ≠ 0) :
    lpMaxDeg (f + g) ≤ max (lpMaxDeg f) (lpMaxDeg g) := by
  by_cases hf : f = 0
  · subst hf; rw [zero_add, lpMaxDeg_zero]; exact le_max_right _ _
  · by_cases hg : g = 0
    · subst hg; rw [add_zero, lpMaxDeg_zero]; exact le_max_left _ _
    · have hf' := lp_support_nonempty hf
      have hg' := lp_support_nonempty hg
      have hfg' := lp_support_nonempty hfg
      unfold lpMaxDeg
      rw [dif_pos hfg', dif_pos hf', dif_pos hg']
      apply Finset.max'_le
      intro k hk
      have hkc : (f + g).coeff k ≠ 0 := Finsupp.mem_support_iff.mp hk
      rw [lp_coeff_add, Finsupp.add_apply] at hkc
      have hne : f.coeff k ≠ 0 ∨ g.coeff k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hkc (by rw [h.1, h.2, add_zero])
      rcases hne with h | h
      · exact le_max_of_le_left (Finset.le_max' _ _
          (Finsupp.mem_support_iff.mpr h))
      · exact le_max_of_le_right (Finset.le_max' _ _
          (Finsupp.mem_support_iff.mpr h))

theorem lpMinDeg_add_le {f g : LaurentPolynomial K} (hfg : f + g ≠ 0) :
    lpMinDeg (f + g) ≤ max (lpMinDeg f) (lpMinDeg g) := by
  by_cases hf : f = 0
  · subst hf; rw [zero_add, lpMinDeg_zero]; exact le_max_right _ _
  · by_cases hg : g = 0
    · subst hg; rw [add_zero, lpMinDeg_zero]; exact le_max_left _ _
    · have hf' := lp_support_nonempty hf
      have hg' := lp_support_nonempty hg
      have hfg' := lp_support_nonempty hfg
      have hmin : min (f.coeff.support.min' hf') (g.coeff.support.min' hg')
          ≤ (f + g).coeff.support.min' hfg' := by
        apply Finset.le_min'
        intro k hk
        have hkc : (f + g).coeff k ≠ 0 := Finsupp.mem_support_iff.mp hk
        rw [lp_coeff_add, Finsupp.add_apply] at hkc
        have hne : f.coeff k ≠ 0 ∨ g.coeff k ≠ 0 := by
          by_contra h
          push_neg at h
          exact hkc (by rw [h.1, h.2, add_zero])
        rcases hne with h | h
        · exact min_le_of_left_le (Finset.min'_le _ _
            (Finsupp.mem_support_iff.mpr h))
        · exact min_le_of_right_le (Finset.min'_le _ _
            (Finsupp.mem_support_iff.mpr h))
      unfold lpMinDeg
      rw [dif_pos hfg', dif_pos hf', dif_pos hg', max_neg_neg, neg_le_neg_iff]
      exact hmin

theorem lpMaxDeg_neg (f : LaurentPolynomial K) : lpMaxDeg (-f) = lpMaxDeg f := by
  have hsup : (-f).coeff.support = f.coeff.support := by
    rw [lp_coeff_neg, Finsupp.support_neg]
  by_cases hf : f = 0
  · subst hf; rw [neg_zero]
  · unfold lpMaxDeg
    rw [hsup]

theorem lpMinDeg_neg (f : LaurentPolynomial K) : lpMinDeg (-f) = lpMinDeg f := by
  have hsup : (-f).coeff.support = f.coeff.support := by
    rw [lp_coeff_neg, Finsupp.support_neg]
  by_cases hf : f = 0
  · subst hf; rw [neg_zero]
  · unfold lpMinDeg
    rw [hsup]

/-- `ValCore` instances: max-degree and minus-min-degree on `LaurentPolynomial K`. -/
theorem valCore_lpMaxDeg : ValCore (LaurentPolynomial K) lpMaxDeg where
  zero := lpMaxDeg_zero
  mul f g hf hg := lpMaxDeg_mul hf hg
  add f g hfg := lpMaxDeg_add_le hfg
  neg f := lpMaxDeg_neg f
  one := by
    rw [show (1 : LaurentPolynomial K) = LaurentPolynomial.C 1 from
      (map_one LaurentPolynomial.C).symm]
    exact lpMaxDeg_C one_ne_zero
  two := by
    rw [show (2 : LaurentPolynomial K) = LaurentPolynomial.C 2 from
      (map_ofNat LaurentPolynomial.C 2).symm]
    exact lpMaxDeg_C (by norm_num : (2 : K) ≠ 0)

theorem valCore_lpMinDeg : ValCore (LaurentPolynomial K) lpMinDeg where
  zero := lpMinDeg_zero
  mul f g hf hg := lpMinDeg_mul hf hg
  add f g hfg := lpMinDeg_add_le hfg
  neg f := lpMinDeg_neg f
  one := by
    rw [show (1 : LaurentPolynomial K) = LaurentPolynomial.C 1 from
      (map_one LaurentPolynomial.C).symm]
    exact lpMinDeg_C one_ne_zero
  two := by
    rw [show (2 : LaurentPolynomial K) = LaurentPolynomial.C 2 from
      (map_ofNat LaurentPolynomial.C 2).symm]
    exact lpMinDeg_C (by norm_num : (2 : K) ≠ 0)

/-! ### §4. The square-root construction (E11/E19 existence)

Given coefficient data `Pcoef` with `Pcoef 6 = u0²`, the recursion
`u k = inv2u0 * (q k - ∑_{j<k-1} u (j+1) * u (k-1-j))` (the corrected form of
the paper's §5 recursion, cf. Leg C `e11_recursion_step`) has a solution `u`
built by primitive recursion over prefix functions; its power series squares to
`mk q`, and `C = single (-3) 1 * ↑U` satisfies `C² = Pser` with the prescribed
coefficients. Generic over any commutative ring with an explicit inverse of
`2*u0` (no field structure needed). -/

/-- The corrected recursion step, in ℕ form (Leg C `e11_recursion_step`,
generalised from `(2*C3)⁻¹` to an explicit inverse `inv2u0` of `2*u0`). -/
theorem rec_step {A : Type*} [CommRing A] (u0 inv2u0 : A) (h2u0 : (2 * u0) * inv2u0 = 1)
    (u q : ℕ → A) (k : ℕ) (hk : 1 ≤ k) (hu0 : u 0 = u0)
    (hrec : u k = inv2u0 * (q k - ∑ j ∈ Finset.range (k - 1), u (j + 1) * u (k - 1 - j))) :
    ∑ j ∈ Finset.range (k + 1), u j * u (k - j) = q k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hrec' : u (k' + 1) = inv2u0 * (q (k' + 1) -
      ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j)) := by
    simpa only [Nat.add_sub_cancel] using hrec
  have hsplit : ∑ j ∈ Finset.range (k' + 1 + 1), u j * u (k' + 1 - j)
      = u 0 * u (k' + 1) + (∑ j ∈ Finset.range k', u (j + 1) * u (k' - j))
        + u (k' + 1) * u 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ, Nat.sub_zero, Nat.sub_self]
    ring
  have h2 : u0 * (inv2u0 * (q (k' + 1) - ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j)))
      + (inv2u0 * (q (k' + 1) - ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j))) * u0
      = q (k' + 1) - ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j) := by
    have key : (2 * u0) * (inv2u0 * (q (k' + 1) -
        ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j)))
        = q (k' + 1) - ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j) := by
      rw [← mul_assoc, h2u0, one_mul]
    have h3 : u0 * (inv2u0 * (q (k' + 1) - ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j)))
        + (inv2u0 * (q (k' + 1) - ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j))) * u0
        = (2 * u0) * (inv2u0 * (q (k' + 1) -
            ∑ j ∈ Finset.range k', u (j + 1) * u (k' - j))) := by
      ring
    rw [h3, key]
  rw [hsplit, hu0, hrec']
  linear_combination h2

/-- The power series built from a recursion solution squares to the data series. -/
theorem powser_sq {A : Type*} [CommRing A] (u0 inv2u0 : A) (h2u0 : (2 * u0) * inv2u0 = 1)
    (u q : ℕ → A) (hu0 : u 0 = u0) (hq0 : q 0 = u0 ^ 2)
    (hrec : ∀ k, 1 ≤ k → u k = inv2u0 * (q k - ∑ j ∈ Finset.range (k - 1), u (j + 1) * u (k - 1 - j))) :
    (PowerSeries.mk u) ^ 2 = PowerSeries.mk q := by
  apply PowerSeries.ext
  intro n
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  cases n with
  | zero =>
      simp [hu0, hq0, pow_two]
  | succ n =>
      exact rec_step u0 inv2u0 h2u0 u q (n + 1) (by omega) hu0 (hrec (n + 1) (by omega))

/-- The prefix-function recursion: `recSeq n` is the solution on indices `≤ n`. -/
noncomputable def recSeq {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A) :
    ℕ → (ℕ → A)
  | 0 => fun _ => u0
  | (n + 1) => Function.update (recSeq u0 inv2u0 q n) (n + 1)
      (inv2u0 * (q (n + 1) - ∑ j ∈ Finset.range n,
        recSeq u0 inv2u0 q n (j + 1) * recSeq u0 inv2u0 q n (n - j)))

theorem recSeq_extend {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A) (n k : ℕ)
    (hk : k ≤ n) :
    recSeq u0 inv2u0 q (n + 1) k = recSeq u0 inv2u0 q n k := by
  simp only [recSeq]
  rw [Function.update_of_ne (by omega : k ≠ n + 1)]

theorem recSeq_coh_le {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A)
    {m n k : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    recSeq u0 inv2u0 q m k = recSeq u0 inv2u0 q n k := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [recSeq_extend u0 inv2u0 q n k (by omega : k ≤ n)]
      exact ih

theorem recSeq_coh {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A)
    {m n k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    recSeq u0 inv2u0 q m k = recSeq u0 inv2u0 q n k := by
  rcases le_total m n with h | h
  · exact recSeq_coh_le u0 inv2u0 q hkm h
  · exact (recSeq_coh_le u0 inv2u0 q hkn h).symm

/-- The diagonal solution: `recDiag k = recSeq k k`. -/
noncomputable def recDiag {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A) (k : ℕ) : A :=
  recSeq u0 inv2u0 q k k

theorem recDiag_zero {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A) :
    recDiag u0 inv2u0 q 0 = u0 := rfl

theorem recDiag_succ {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A) (n : ℕ) :
    recDiag u0 inv2u0 q (n + 1)
      = inv2u0 * (q (n + 1) - ∑ j ∈ Finset.range n,
          recDiag u0 inv2u0 q (j + 1) * recDiag u0 inv2u0 q (n - j)) := by
  have h1 : recSeq u0 inv2u0 q (n + 1) (n + 1)
      = inv2u0 * (q (n + 1) - ∑ j ∈ Finset.range n,
          recSeq u0 inv2u0 q n (j + 1) * recSeq u0 inv2u0 q n (n - j)) := by
    simp only [recSeq]
    exact Function.update_self (n + 1) _ _
  have hsum : (∑ j ∈ Finset.range n,
        recSeq u0 inv2u0 q n (j + 1) * recSeq u0 inv2u0 q n (n - j))
      = ∑ j ∈ Finset.range n,
          recSeq u0 inv2u0 q (j + 1) (j + 1) * recSeq u0 inv2u0 q (n - j) (n - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    rw [recSeq_coh u0 inv2u0 q (k := j + 1) (by omega : j + 1 ≤ n) (by omega : j + 1 ≤ j + 1),
      recSeq_coh u0 inv2u0 q (k := n - j) (by omega : n - j ≤ n) (by omega : n - j ≤ n - j)]
  unfold recDiag
  rw [h1, hsum]

/-- The diagonal solution satisfies the recursion at every `k ≥ 1`. -/
theorem recDiag_rec {A : Type*} [CommRing A] (u0 inv2u0 : A) (q : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    recDiag u0 inv2u0 q k = inv2u0 * (q k - ∑ j ∈ Finset.range (k - 1),
      recDiag u0 inv2u0 q (j + 1) * recDiag u0 inv2u0 q (k - 1 - j)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact recDiag_succ u0 inv2u0 q n

/-- Coefficients of a power series, viewed as a Laurent series, vanish at
    negative indices (via `embDomain`: the support lies in the image of `ℕ`). -/
theorem coeff_ofPowerSeries_neg {A : Type*} [CommRing A] (f : PowerSeries A) (m : ℤ)
    (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ A f).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  intro hmem
  obtain ⟨n, -, hn⟩ := hmem
  have hn' : (n : ℤ) = m := hn
  rw [← hn'] at hm
  omega

/-- Generic square-root existence: from coefficient data `Pcoef` with top
coefficient `u0²`, there is a Laurent series `C` with `C² = Pser`, whose
`x^{k-3}`-coefficient is the recursion solution `recDiag k`, and `C_{-3} = u0`.
The support hypotheses `hPsupp`/`hPneg` are not needed for the square itself;
they are carried as data for the assembly's coefficient bounds. -/
theorem exists_sqrt_series {A : Type*} [CommRing A] (u0 inv2u0 : A) (h2u0 : (2 * u0) * inv2u0 = 1)
    (Pcoef : ℤ → A) (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = u0 ^ 2) :
    ∃ C : LaurentSeries A,
      C ^ 2 = HahnSeries.single (-6 : ℤ) (1 : A) *
          (HahnSeries.ofPowerSeries ℤ A) (PowerSeries.mk fun n => Pcoef (6 - (n : ℤ))) ∧
      (∀ k : ℕ, C.coeff ((k : ℤ) - 3) = recDiag u0 inv2u0 (fun n => Pcoef (6 - (n : ℤ))) k) ∧
      C.coeff (-3) = u0 ∧
      (∀ m : ℤ, m < -3 → C.coeff m = 0) := by
  set q : ℕ → A := fun n => Pcoef (6 - (n : ℤ)) with hq
  set u : ℕ → A := recDiag u0 inv2u0 q with hu
  have hu0 : u 0 = u0 := recDiag_zero _ _ _
  have hq0' : q 0 = u0 ^ 2 := by
    simp only [hq]
    simpa using hq0
  have hrec : ∀ k, 1 ≤ k → u k = inv2u0 * (q k - ∑ j ∈ Finset.range (k - 1), u (j + 1) * u (k - 1 - j)) := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact recDiag_succ u0 inv2u0 q n
  have hsq : (PowerSeries.mk u) ^ 2 = PowerSeries.mk q := powser_sq u0 inv2u0 h2u0 u q hu0 hq0' hrec
  have hcoeff : ∀ k : ℕ, (HahnSeries.single (-3 : ℤ) (1 : A) *
      (HahnSeries.ofPowerSeries ℤ A) (PowerSeries.mk u)).coeff ((k : ℤ) - 3) = u k := by
    intro k
    rw [coeff_single_mul]
    simp [coeff_coe_powerSeries, PowerSeries.coeff_mk]
  have hneg : ∀ m : ℤ, m < -3 →
      (HahnSeries.single (-3 : ℤ) (1 : A) *
        (HahnSeries.ofPowerSeries ℤ A) (PowerSeries.mk u)).coeff m = 0 := by
    intro m hm
    rw [coeff_single_mul, one_mul]
    exact coeff_ofPowerSeries_neg _ _ (by omega)
  refine ⟨HahnSeries.single (-3 : ℤ) (1 : A) * (HahnSeries.ofPowerSeries ℤ A) (PowerSeries.mk u),
    ?_, hcoeff, ?_, hneg⟩
  · have hcomm : HahnSeries.single (-3 : ℤ) (1 : A) * (HahnSeries.ofPowerSeries ℤ A) (PowerSeries.mk u)
        = (HahnSeries.ofPowerSeries ℤ A) (PowerSeries.mk u) * HahnSeries.single (-3 : ℤ) (1 : A) := by
      ext m
      rw [coeff_single_mul, coeff_mul_single]
      ring
    have hsingle : HahnSeries.single (-3 : ℤ) (1 : A) * HahnSeries.single (-3 : ℤ) (1 : A)
        = HahnSeries.single (-6 : ℤ) (1 : A) := by
      rw [single_mul_single]
      have h1 : (-3 : ℤ) + (-3) = -6 := by norm_num
      have h2 : (1 : A) * 1 = 1 := mul_one 1
      rw [h1, h2]
    rw [sq, hcomm, mul_mul_mul_comm, hsingle, ← map_mul, ← pow_two, hsq]
    rw [mul_comm]
  · simpa [hu0] using hcoeff 0

/-- §6 data: `2*y` is a unit of `LaurentPolynomial K`, with inverse `C(1/2) * T(-1)`. -/
theorem h2y_s6 : (2 * T 1 : LaurentPolynomial K) *
    (LaurentPolynomial.C (1 / 2) * T (-1)) = 1 := by
  have h2 : (2 : LaurentPolynomial K) = LaurentPolynomial.C 2 :=
    (map_ofNat LaurentPolynomial.C 2).symm
  have hT : T (1 : ℤ) * T (-1 : ℤ) = (1 : LaurentPolynomial K) := by
    rw [← T_add, show (1 : ℤ) + (-1) = 0 by norm_num, T_zero]
  have e1 : LaurentPolynomial.C 2 * LaurentPolynomial.C (1 / 2) = (1 : LaurentPolynomial K) := by
    rw [← map_mul, show (2 : K) * (1 / 2) = 1 by norm_num, map_one]
  rw [h2, mul_mul_mul_comm, e1, hT, mul_one]

/-- §6 square-root existence (E19 (1)): `C` with `C² = P`, `C_{-3} = y`. -/
theorem e19_sqrt_s6 (Pcoef : ℤ → LaurentPolynomial K)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = (T 1 : LaurentPolynomial K) ^ 2) :
    ∃ C : LaurentSeries (LaurentPolynomial K),
      C ^ 2 = HahnSeries.single (-6 : ℤ) (1 : LaurentPolynomial K) *
          (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial K))
            (PowerSeries.mk fun n => Pcoef (6 - (n : ℤ))) ∧
      (∀ k : ℕ, C.coeff ((k : ℤ) - 3) =
        recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) (fun n => Pcoef (6 - (n : ℤ))) k) ∧
      C.coeff (-3) = T 1 ∧
      (∀ m : ℤ, m < -3 → C.coeff m = 0) :=
  exists_sqrt_series (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) h2y_s6 Pcoef hPsupp hPneg hq0

/-- `(2 : LaurentPolynomial K) ≠ 0` (norm_num cannot see it; via `degree_C`). -/
theorem lp_two_ne_zero : (2 : LaurentPolynomial K) ≠ 0 := by
  rw [show (2 : LaurentPolynomial K) = LaurentPolynomial.C 2 from
    (map_ofNat LaurentPolynomial.C 2).symm]
  intro h
  have hdeg := congrArg LaurentPolynomial.degree h
  rw [degree_C (by norm_num : (2 : K) ≠ 0)] at hdeg
  have h0 : (0 : LaurentPolynomial K).degree = ⊥ := by
    show (0 : LaurentPolynomial K).coeff.support.max = ⊥
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.support_zero, Finset.max_empty]
  rw [h0] at hdeg
  exact absurd hdeg (by simp)

/-- §6 existence + coefficient bounds (E19 (1)–(4) at the coefficient level):
`C` with `C² = P`, `C_{-3} = y`, and the `(b_k)`/`(c_k)` bounds
`lpMaxDeg (C_{3-n}) ≤ 1 + 2n`, `lpMinDeg (C_{3-n}) ≤ n - 1` from
`valcore_finite_bounds` at the two LP valuations. The `P`-bounds `hP21`/`hP1m1`
are the paper's Newton-polygon data, carried as hypotheses. -/
theorem e19_existence_bounds_s6 (Pcoef : ℤ → LaurentPolynomial K)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = (T 1 : LaurentPolynomial K) ^ 2)
    (hP21 : ∀ k : ℤ, 1 ≤ k → lpMaxDeg (Pcoef (6 - k)) ≤ 2 + 2 * k)
    (hP1m1 : ∀ k : ℤ, 1 ≤ k → lpMinDeg (Pcoef (6 - k)) ≤ k - 2) :
    ∃ C : LaurentSeries (LaurentPolynomial K),
      C ^ 2 = HahnSeries.single (-6 : ℤ) (1 : LaurentPolynomial K) *
          (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial K))
            (PowerSeries.mk fun n => Pcoef (6 - (n : ℤ))) ∧
      (∀ k : ℕ, C.coeff ((k : ℤ) - 3) =
        recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) (fun n => Pcoef (6 - (n : ℤ))) k) ∧
      C.coeff (-3) = T 1 ∧
      (∀ n : ℕ, lpMaxDeg (C.coeff ((n : ℤ) - 3)) ≤ 1 + 2 * (n : ℤ)) ∧
      (∀ n : ℕ, lpMinDeg (C.coeff ((n : ℤ) - 3)) ≤ (n : ℤ) - 1) ∧
      (∀ m : ℤ, m < -3 → C.coeff m = 0) := by
  obtain ⟨C, hC2, hCcoeff, hC3, hCneg⟩ := e19_sqrt_s6 Pcoef hPsupp hPneg hq0
  -- The unit `d = (2y)⁻¹`, as an explicit unit (so its value and its inverse's
  -- value are both definitional).
  set d : (LaurentPolynomial K)ˣ :=
    ⟨LaurentPolynomial.C (1 / 2) * T (-1), 2 * T 1,
      by rw [mul_comm]; exact h2y_s6, h2y_s6⟩ with hd
  have hdval : ((d : (LaurentPolynomial K)ˣ) : LaurentPolynomial K)
      = LaurentPolynomial.C (1 / 2) * T (-1) := rfl
  have hd21 : lpMaxDeg ((d : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = -1 := by
    have h1 : lpMaxDeg (2 * T 1 : LaurentPolynomial K) = 1 := by
      rw [valCore_lpMaxDeg.mul _ _ lp_two_ne_zero (isUnit_T 1).ne_zero,
        show (2 : LaurentPolynomial K) = LaurentPolynomial.C 2 from
          (map_ofNat LaurentPolynomial.C 2).symm,
        lpMaxDeg_C (by norm_num : (2 : K) ≠ 0), lpMaxDeg_T]
      norm_num
    have h2 := valCore_lpMaxDeg.inv_unit (d⁻¹)
    rw [inv_inv] at h2
    have h3 : ((d⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = 2 * T 1 := rfl
    rw [h3, h1] at h2
    omega
  have hd1m1 : lpMinDeg ((d : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = 1 := by
    have h1 : lpMinDeg (2 * T 1 : LaurentPolynomial K) = -1 := by
      rw [valCore_lpMinDeg.mul _ _ lp_two_ne_zero (isUnit_T 1).ne_zero,
        show (2 : LaurentPolynomial K) = LaurentPolynomial.C 2 from
          (map_ofNat LaurentPolynomial.C 2).symm,
        lpMinDeg_C (by norm_num : (2 : K) ≠ 0), lpMinDeg_T]
      norm_num
    have h2 := valCore_lpMinDeg.inv_unit (d⁻¹)
    rw [inv_inv] at h2
    have h3 : ((d⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = 2 * T 1 := rfl
    rw [h3, h1] at h2
    omega
  set q : ℕ → LaurentPolynomial K := fun n => Pcoef (6 - (n : ℤ)) with hq
  set Cfun : ℤ → LaurentPolynomial K :=
    fun n => recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q ((3 - n).toNat) with hCfun
  have hCfun3 : Cfun 3 = T 1 := recDiag_zero _ _ _
  have hCfun_n : ∀ n : ℕ, Cfun (3 - (n : ℤ))
      = recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q n := by
    intro n
    show recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q ((3 - (3 - (n : ℤ))).toNat) = _
    congr 1
    omega
  have hCfun_rec : ∀ k : ℤ, 1 ≤ k → Cfun (3 - k) =
      (Pcoef (6 - k) - ∑ j ∈ Finset.Icc 1 (k - 1), Cfun (3 - j) * Cfun (3 - k + j)) *
        ((d : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) := by
    intro k hk
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.toNat, (Int.toNat_of_nonneg (by omega : 0 ≤ k)).symm⟩
    subst hm
    have hm1 : 1 ≤ m := by exact_mod_cast hk
    have hC1 : Cfun (3 - (m : ℤ))
        = recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q m := hCfun_n m
    have hsum : (∑ j ∈ Finset.range (m - 1),
          recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q (j + 1) *
            recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q (m - 1 - j))
        = ∑ j ∈ Finset.Icc 1 ((m : ℤ) - 1), Cfun (3 - j) * Cfun (3 - (m : ℤ) + j) := by
      have hIcc : Finset.Icc (1 : ℤ) ((m : ℤ) - 1)
          = (Finset.range (m - 1)).image (fun i : ℕ => (i : ℤ) + 1) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩
          refine ⟨j.toNat - 1, by omega, by omega⟩
        · rintro ⟨i, hi, rfl⟩
          constructor <;> push_cast <;> omega
      rw [hIcc, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < m - 1 := Finset.mem_range.mp hi
        have e1 : Cfun (3 - ((i : ℤ) + 1))
            = recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q (i + 1) := by
          show recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q
              ((3 - (3 - ((i : ℤ) + 1))).toNat) = _
          congr 1
          omega
        have e2 : Cfun (3 - (m : ℤ) + ((i : ℤ) + 1))
            = recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q (m - 1 - i) := by
          show recDiag (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q
              ((3 - (3 - (m : ℤ) + ((i : ℤ) + 1))).toNat) = _
          congr 1
          omega
        rw [e1, e2]
      · intro a _ b _ h
        have h' : (a : ℤ) + 1 = (b : ℤ) + 1 := h
        omega
    rw [hC1, recDiag_rec (T 1) (LaurentPolynomial.C (1 / 2) * T (-1)) q m hm1, hdval, mul_comm,
      hsum]
  have hbounds := valcore_finite_bounds valCore_lpMaxDeg valCore_lpMinDeg (y := T 1)
    (lpMaxDeg_T 1) (lpMinDeg_T 1) d d hd21 hd1m1 rfl Cfun Pcoef hCfun3 hCfun_rec hP21 hP1m1
  refine ⟨C, hC2, hCcoeff, hC3, ?_, ?_, hCneg⟩
  · intro n
    have h := (hbounds n).1
    rw [hCfun_n n, ← hCcoeff n] at h
    exact h
  · intro n
    have h := (hbounds n).2
    rw [hCfun_n n, ← hCcoeff n] at h
    exact h


/-! ## §5. The Poisson bracket on Laurent series (E23).

Conventions: `S = LaurentSeries (LaurentPolynomial K)`; `t` is the series variable
(`t = x⁻¹`, so `x = single (-1) 1`, `y = C (T 1)`); a monomial `xⁿ yʲ` with scalar `a`
is `mono n j a = single (-n) (C a * T j)`.

`∂/∂x = -t² ∂/∂t`, so `derivX f = -(single 2 1) * (derivative K) f` where
`LaurentSeries.derivative K = hasseDeriv K 1` (`derivative_apply`).
`derivY` is coefficientwise `lpDeriv` (the y-derivation on Laurent polynomials).

Verdict: the monomial bracket formula (`bracket_mono`) and the E23 instance
(`e23_instance`) are KERNEL. The series-level reduction (`e23_series_reduction`)
is CONDITIONAL on the bracket-degree bound `hdeg` (the bracket of `x⁶y²` with a
series of x-degree `≤ -4` has no x-coefficient above degree `1`): that bound needs
the Leibniz rule for `LaurentSeries.derivative`, which Mathlib 4.34.0 does NOT
supply (no Leibniz lemma for `hasseDeriv`/`derivative` on Hahn series). -/

/-- A monomial `a * xⁿ * yʲ` as a Laurent series in `t = x⁻¹`. -/
noncomputable def mono (n j : ℤ) (a : K) : LaurentSeries (LaurentPolynomial K) :=
  HahnSeries.single (-n) (LaurentPolynomial.C a * T j)

/-- `mono` unfolded to a `HahnSeries.single` (rewrite helper). -/
theorem mono_eq_single (n j : ℤ) (a : K) :
    mono n j a = HahnSeries.single (-n) (LaurentPolynomial.C a * T j) := rfl

/-- Coefficients of a monomial. -/
theorem mono_coeff (n j : ℤ) (a : K) (m : ℤ) :
    (mono n j a).coeff m = if m = -n then LaurentPolynomial.C a * T j else 0 := by
  by_cases hm : m = -n
  · subst hm
    simp [mono]
  · simp [mono, hm]

/-- The y-derivation on Laurent polynomials: `T^j ↦ j • T^(j-1)`, coefficientwise. -/
noncomputable def lpDeriv (f : LaurentPolynomial K) : LaurentPolynomial K :=
  f.coeff.sum fun j a => LaurentPolynomial.C ((j : K) * a) * T (j - 1)

theorem lpDeriv_zero : lpDeriv (0 : LaurentPolynomial K) = 0 := by simp [lpDeriv]

theorem lpDeriv_add (f g : LaurentPolynomial K) :
    lpDeriv (f + g) = lpDeriv f + lpDeriv g := by
  unfold lpDeriv
  rw [AddMonoidAlgebra.coeff_add]
  refine Finsupp.sum_add_index' ?_ ?_
  · intro j; simp
  · intro j b₁ b₂; rw [mul_add, map_add, add_mul]

theorem lpDeriv_C_mul_T (a : K) (j : ℤ) :
    lpDeriv (LaurentPolynomial.C a * T j) =
      LaurentPolynomial.C ((j : K) * a) * T (j - 1) := by
  have hcoeff : (LaurentPolynomial.C a * T j).coeff = Finsupp.single j a := by
    rw [← single_eq_C_mul_T a j, AddMonoidAlgebra.coeff_single]
  unfold lpDeriv
  rw [hcoeff, Finsupp.sum_single_index]
  simp

theorem lpDeriv_T (j : ℤ) :
    lpDeriv (T j) = LaurentPolynomial.C (j : K) * T (j - 1) := by
  calc lpDeriv (T j) = lpDeriv (LaurentPolynomial.C 1 * T j) := by
        congr 1
        simp
      _ = LaurentPolynomial.C ((j : K) * 1) * T (j - 1) := lpDeriv_C_mul_T 1 j
      _ = LaurentPolynomial.C (j : K) * T (j - 1) := by simp

theorem lpDeriv_C (a : K) : lpDeriv (LaurentPolynomial.C a) = 0 := by
  calc lpDeriv (LaurentPolynomial.C a) =
        lpDeriv (LaurentPolynomial.C a * T 0) := by
        congr 1
        simp
      _ = LaurentPolynomial.C (((0 : ℤ) : K) * a) * T (0 - 1) := lpDeriv_C_mul_T a 0
      _ = 0 := by simp

/-- Product of two `C u * T m` terms (the coefficient arithmetic of the bracket). -/
theorem C_mul_T_mul_C_mul_T (u v : K) (m n : ℤ) :
    (LaurentPolynomial.C u * T m) * (LaurentPolynomial.C v * T n) =
      LaurentPolynomial.C (u * v) * T (m + n) := by
  rw [mul_mul_mul_comm, ← map_mul, ← T_add]

/-- Scalar action on a `C u * T m` term. -/
theorem C_mul_T_smul (r u : K) (m : ℤ) :
    r • (LaurentPolynomial.C u * T m) = LaurentPolynomial.C (r * u) * T m := by
  rw [LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]

/-- `∂/∂x = -t² ∂/∂t` on Laurent series. -/
noncomputable def derivX (f : LaurentSeries (LaurentPolynomial K)) :
    LaurentSeries (LaurentPolynomial K) :=
  -(HahnSeries.single (2 : ℤ) (1 : LaurentPolynomial K)) * LaurentSeries.derivative K f

/-- The y-derivation, lifted coefficientwise to Laurent series. -/
noncomputable def derivY (f : LaurentSeries (LaurentPolynomial K)) :
    LaurentSeries (LaurentPolynomial K) :=
  HahnSeries.mk (fun n => lpDeriv (f.coeff n)) (by
    apply Set.IsPWO.mono f.isPWO_support
    intro n hn
    simp only [Function.mem_support] at hn ⊢
    intro h0
    exact hn (by rw [h0, lpDeriv_zero]))

theorem derivY_coeff (f : LaurentSeries (LaurentPolynomial K)) (n : ℤ) :
    (derivY f).coeff n = lpDeriv (f.coeff n) := rfl

/-- The first Hasse derivative of a single: `D(single n c) = single (n-1) (n • c)`. -/
theorem hasseDeriv_single_one (n : ℤ) (c : LaurentPolynomial K) :
    LaurentSeries.derivative K (HahnSeries.single n c) =
      HahnSeries.single (n - 1) (((n : K)) • c) := by
  rw [derivative_apply, hasseDeriv_single, Ring.choose_one_right, Nat.cast_one,
    ← Int.cast_smul_eq_zsmul K]

/-- `∂/∂x (xⁿyʲ) = n xⁿ⁻¹yʲ` (no outer negation: the `-t²` sign is absorbed into
    the coefficient via `single_neg`). -/
theorem derivX_mono (n j : ℤ) (a : K) :
    derivX (mono n j a) =
      HahnSeries.single (1 - n) (((n : K)) • (LaurentPolynomial.C a * T j)) := by
  unfold derivX
  rw [mono_eq_single, hasseDeriv_single_one, ← HahnSeries.single_neg, single_mul_single,
    show (2 : ℤ) + (-n - 1) = 1 - n from by ring, neg_one_mul, ← neg_smul, Int.cast_neg,
    neg_neg]

theorem derivY_mono (n j : ℤ) (a : K) :
    derivY (mono n j a) =
      HahnSeries.single (-n) (LaurentPolynomial.C ((j : K) * a) * T (j - 1)) := by
  apply HahnSeries.ext
  funext m
  rw [derivY_coeff, mono_coeff, HahnSeries.coeff_single]
  by_cases hm : m = -n
  · rw [if_pos hm, lpDeriv_C_mul_T, if_pos hm]
  · rw [if_neg hm, lpDeriv_zero, if_neg hm]

/-- Scalar action on a single (no `smul_single` in Mathlib 4.34.0). -/
theorem smul_single (r : K) (m : ℤ) (s : LaurentPolynomial K) :
    r • HahnSeries.single m s = HahnSeries.single m (r • s) := by
  apply HahnSeries.ext
  funext k
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]
  by_cases hk : k = m
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, smul_zero]

/-- The Poisson bracket on Laurent series. -/
noncomputable def bracket (f g : LaurentSeries (LaurentPolynomial K)) :
    LaurentSeries (LaurentPolynomial K) :=
  derivX f * derivY g - derivY f * derivX g

theorem derivX_add (f g : LaurentSeries (LaurentPolynomial K)) :
    derivX (f + g) = derivX f + derivX g := by
  unfold derivX
  rw [map_add, mul_add]

theorem derivY_add (f g : LaurentSeries (LaurentPolynomial K)) :
    derivY (f + g) = derivY f + derivY g := by
  apply HahnSeries.ext
  funext n
  rw [derivY_coeff, HahnSeries.coeff_add, lpDeriv_add, HahnSeries.coeff_add,
    derivY_coeff, derivY_coeff]

theorem bracket_add_left (f₁ f₂ g : LaurentSeries (LaurentPolynomial K)) :
    bracket (f₁ + f₂) g = bracket f₁ g + bracket f₂ g := by
  unfold bracket
  rw [derivX_add, derivY_add, add_mul, add_mul, ← sub_add_sub_comm]

theorem bracket_add_right (f g₁ g₂ : LaurentSeries (LaurentPolynomial K)) :
    bracket f (g₁ + g₂) = bracket f g₁ + bracket f g₂ := by
  unfold bracket
  rw [derivX_add, derivY_add, mul_add, mul_add, ← sub_add_sub_comm]

/-- Monomial bracket formula (KERNEL): `[xⁿyʲ, xᶜyᵈ] = (nd - jc) xⁿ⁺ᶜ⁻¹ yʲ⁺ᵈ⁻¹`. -/
theorem bracket_mono (n j c d : ℤ) (a b : K) :
    bracket (mono n j a) (mono c d b) =
      (((n * d - j * c : ℤ) : K)) • mono (n + c - 1) (j + d - 1) (a * b) := by
  have e1 : (1 : ℤ) - n + -c = 1 - n - c := by ring
  have e2 : -n + (1 - c) = 1 - n - c := by ring
  have hE : (j - 1) + d = j + (d - 1) := by ring
  unfold bracket
  rw [derivX_mono, derivY_mono, derivX_mono, derivY_mono, single_mul_single,
    single_mul_single, e1, e2, ← HahnSeries.single_sub, mono_eq_single, smul_single,
    C_mul_T_smul, C_mul_T_smul, C_mul_T_smul, C_mul_T_mul_C_mul_T, C_mul_T_mul_C_mul_T,
    hE, ← sub_mul, ← map_sub]
  congr 1
  · ring
  · congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      ring

/-- E23 instance (KERNEL): `[x⁶y², (1/2)y⁻¹x⁻⁴] = x`. -/
theorem e23_instance :
    bracket (mono 6 2 1) (mono (-4) (-1) (1/2 : K)) = mono 1 0 1 := by
  rw [bracket_mono]
  have h1 : (6 : ℤ) * (-1) - 2 * (-4) = 2 := by norm_num
  have h2 : (6 : ℤ) + -4 - 1 = 1 := by norm_num
  have h3 : (2 : ℤ) + -1 - 1 = 0 := by norm_num
  have h4 : (1 : K) * (1/2) = 1/2 := one_mul _
  rw [h1, h2, h3, h4, mono_eq_single, smul_single, C_mul_T_smul]
  have h5 : (((2 : ℤ) : K)) * (1/2 : K) = 1 := by norm_num
  rw [h5, ← mono_eq_single]

/-- E23 series reduction (CONDITIONAL on the bracket-degree bound `hdeg`).
    The bracket is additive in each argument (KERNEL: `bracket_add_left/right`), so
    `[x⁶y², F] = [x⁶y², F₋₄x⁻⁴] + [x⁶y², F - F₋₄x⁻⁴] = x + R`, where the first term
    is `x` (KERNEL: `e23_instance`) and `R` has no coefficient below t-degree `-1`
    (i.e. no x-coefficient above degree `1`) by `hdeg`. The bound `hdeg` is NOT
    proved here: it needs the Leibniz rule for `LaurentSeries.derivative`, which
    Mathlib 4.34.0 does not supply. Coefficient indices are t-exponents
    (`t = x⁻¹`): `F` of x-degree `≤ -4` means `F.coeff m = 0` for `m < 4`. -/
theorem e23_series_reduction (F : LaurentSeries (LaurentPolynomial K))
    (hFtop : ∀ m : ℤ, m < 4 → F.coeff m = 0)
    (hdeg : ∀ G : LaurentSeries (LaurentPolynomial K),
      (∀ m : ℤ, m < 4 → G.coeff m = 0) → ∀ m : ℤ, m < -1 →
        (bracket (mono 6 2 1) G).coeff m = 0) :
    ∃ R : LaurentSeries (LaurentPolynomial K),
      bracket (mono 6 2 1) F = mono 1 0 1 + R ∧ ∀ m : ℤ, m < -1 → R.coeff m = 0 := by
  set G := F - mono (-4) (-1) (1/2 : K) with hG
  have hGtop : ∀ m : ℤ, m < 4 → G.coeff m = 0 := by
    intro m hm
    rw [hG, HahnSeries.coeff_sub, hFtop m hm, mono_coeff, if_neg (by omega), sub_zero]
  have hFdecomp : F = mono (-4) (-1) (1/2 : K) + G := by rw [hG]; abel
  refine ⟨bracket (mono 6 2 1) G, ?_, hdeg G hGtop⟩
  rw [hFdecomp, bracket_add_right, e23_instance]

/-! ## §6. The F-construction (E11/E19 (c)).

`v_{1,0}` is the x-degree: on a Laurent series `f`, `v10 f = -(f.order)` where
`f.order : ℤ` is Mathlib's `HahnSeries.order` (the least index with a nonzero
coefficient; `order 0 = 0` by definition). It is total on the series ring, and
satisfies `ValCore` generically over any commutative ring with no zero divisors
(`valCore_v10`), so it applies both over `LaurentPolynomial K` (§6) and over
`RatFunc K` (§5, where the coefficient ring is the localisation at C₃).

The F-construction is CONDITIONAL on the named hypothesis bundle `GGV1Inputs`:
the cancellation of Q's terms of x-degree `> -4` against `C³ + α₂C² + α₁C +
α₀ + αm1C⁻¹` (the [GGV3] §1 α-choice) and the nonvanishing of the x⁻⁴ term
(the [GGV1] Prop 1.13 / Prop 2.1 content), both stated at coefficient level.
Given those, `F := Q - (C³ + α₂C² + α₁C + α₀ + αm1C⁻¹)` satisfies
`v10 F = -4` by kernel reasoning from the `order` lemmas (`exists_F`).
The bracket-algebra step `[C^k, C²] = 0` (pure bracket algebra, NOT [GGV1]) is
a separate named hypothesis `bracket_pow_C` below: it needs the Leibniz rule
for `LaurentSeries.derivative`, which Mathlib 4.34.0 does not supply. -/

/-- The (1,0)-valuation: minus the least t-exponent with a nonzero coefficient.
    `v10 f = n` iff the leading x-term of `f` is `xⁿ`. -/
noncomputable def v10 {R : Type*} [CommRing R] [NoZeroDivisors R]
    (f : LaurentSeries R) : ℤ := -(f.order)

theorem v10_zero {R : Type*} [CommRing R] [NoZeroDivisors R] :
    v10 (0 : LaurentSeries R) = 0 := by simp [v10]

/-- `v10` satisfies the corrected valuation axioms, generically. -/
theorem valCore_v10 {R : Type*} [CommRing R] [NoZeroDivisors R] :
    ValCore (LaurentSeries R) (v10 (R := R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show -((0 : LaurentSeries R).order) = 0
    rw [HahnSeries.order_zero, neg_zero]
  · intro a b ha hb
    show -((a * b).order) = -(a.order) + -(b.order)
    rw [HahnSeries.order_mul ha hb, neg_add]
  · intro a b hab
    show -((a + b).order) ≤ max (-(a.order)) (-(b.order))
    by_cases ha : a = 0
    · subst ha
      rw [zero_add, HahnSeries.order_zero, neg_zero]
      exact le_max_right _ _
    · by_cases hb : b = 0
      · subst hb
        rw [add_zero, HahnSeries.order_zero, neg_zero]
        exact le_max_left _ _
      · have h := HahnSeries.min_orderTop_le_orderTop_add (x := a) (y := b)
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hab,
          ← HahnSeries.order_eq_orderTop_of_ne_zero ha,
          ← HahnSeries.order_eq_orderTop_of_ne_zero hb] at h
        rw [← WithTop.coe_min, WithTop.coe_le_coe] at h
        rw [max_neg_neg]
        exact neg_le_neg h
  · intro a
    show -((-a).order) = -(a.order)
    rw [HahnSeries.order_neg]
  · show -((1 : LaurentSeries R).order) = 0
    rw [HahnSeries.order_one, neg_zero]
  · show -(((2 : LaurentSeries R)).order) = 0
    rw [show (2 : LaurentSeries R) = HahnSeries.C 2 from (map_ofNat _ _).symm,
      HahnSeries.order_C, neg_zero]

/-- `v10 C = 3` from the coefficient data: leading coefficient at t-exponent
    `-3` nonzero, nothing below `-3`. -/
theorem v10_of_coeff {R : Type*} [CommRing R] [NoZeroDivisors R]
    (C : LaurentSeries R) (h3 : C.coeff (-3) ≠ 0)
    (hlt : ∀ m : ℤ, m < -3 → C.coeff m = 0) : v10 C = 3 := by
  have hCne : C ≠ 0 := by
    intro h0
    exact h3 (by rw [h0]; simp)
  have hord : C.order = -3 := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero h3
    · by_contra hlt2
      push_neg at hlt2
      have hne : C.coeff (C.order) ≠ 0 := by
        intro h0
        rw [HahnSeries.coeff_order_eq_zero] at h0
        exact hCne h0
      exact hne (hlt _ hlt2)
  show -(C.order) = 3
  rw [hord, neg_neg]

/-- The polynomial part of the Q-expansion: `C³ + α₂C² + α₁C + α₀ + αm1C⁻¹`,
    with the α's as constant series. -/
noncomputable def Fpoly (C : LaurentSeries (RatFunc K)) (α₂ α₁ α₀ αm1 : RatFunc K) :
    LaurentSeries (RatFunc K) :=
  C ^ 3 + HahnSeries.C α₂ * C ^ 2 + HahnSeries.C α₁ * C + HahnSeries.C α₀ +
    HahnSeries.C αm1 * C⁻¹

/-- The [GGV1] Prop 1.13 / Prop 2.1 / [GGV3] §1 inputs for the F-construction,
    stated at coefficient level (these are the premises assembly must discharge
    from the [GGV1]/[GGV3] formalisation; they are NOT proved here):
    the α's cancel Q's terms of x-degree `> -4` (`cancel`), and the x⁻⁴ term
    of the difference is nonzero (`leading`). Coefficient indices are
    t-exponents (`t = x⁻¹`): x-degree `≤ -4` means t-exponent `≥ 4`. -/
structure GGV1Inputs (C Q : LaurentSeries (RatFunc K)) (α₂ α₁ α₀ αm1 : RatFunc K) :
    Prop where
  cancel : ∀ m : ℤ, m < 4 → (Q - Fpoly C α₂ α₁ α₀ αm1).coeff m = 0
  leading : (Q - Fpoly C α₂ α₁ α₀ αm1).coeff 4 ≠ 0

/-- The F-construction (CONDITIONAL on `GGV1Inputs`): `F` exists with
    `Q = C³ + α₂C² + α₁C + α₀ + αm1C⁻¹ + F` and `v10 F = -4`. -/
theorem exists_F (C Q : LaurentSeries (RatFunc K)) (α₂ α₁ α₀ αm1 : RatFunc K)
    (h : GGV1Inputs C Q α₂ α₁ α₀ αm1) :
    ∃ F : LaurentSeries (RatFunc K),
      Q = Fpoly C α₂ α₁ α₀ αm1 + F ∧ v10 F = -4 := by
  refine ⟨Q - Fpoly C α₂ α₁ α₀ αm1, by abel, ?_⟩
  have hFne : Q - Fpoly C α₂ α₁ α₀ αm1 ≠ 0 := by
    intro h0
    apply h.leading
    have hc := congrArg (fun f : LaurentSeries (RatFunc K) => f.coeff 4) h0
    rw [show (0 : LaurentSeries (RatFunc K)).coeff 4 = 0 from by simp] at hc
    exact hc
  have hord : (Q - Fpoly C α₂ α₁ α₀ αm1).order = 4 := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero h.leading
    · by_contra hlt
      push_neg at hlt
      have hne : (Q - Fpoly C α₂ α₁ α₀ αm1).coeff
          ((Q - Fpoly C α₂ α₁ α₀ αm1).order) ≠ 0 := by
        intro h0
        rw [HahnSeries.coeff_order_eq_zero] at h0
        exact hFne h0
      exact hne (h.cancel _ hlt)
  show -((Q - Fpoly C α₂ α₁ α₀ αm1).order) = -4
  rw [hord]

/-- The bracket-algebra step used in the paper's F-construction
    (pure bracket algebra, NOT [GGV1]): `[C^k, C²] = 0` for all `k`.
    This is NOT proved here: it needs the Leibniz rule for
    `LaurentSeries.derivative`, which Mathlib 4.34.0 does not supply
    (no Leibniz lemma for `hasseDeriv`/`derivative` on Hahn series).
    It is recorded as a named hypothesis for assembly. -/
def bracket_pow_C (C : LaurentSeries (LaurentPolynomial K)) : Prop :=
  ∀ k : ℕ, bracket (C ^ k) (C ^ 2) = 0

/-- The §6 series `C` from `e19_existence_bounds_s6` has `v10 C = 3`
    (its leading x-term is `x³y`). -/
theorem v10_C_s6 (Pcoef : ℤ → LaurentPolynomial K)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = (T 1 : LaurentPolynomial K) ^ 2)
    (hP21 : ∀ k : ℤ, 1 ≤ k → lpMaxDeg (Pcoef (6 - k)) ≤ 2 + 2 * k)
    (hP1m1 : ∀ k : ℤ, 1 ≤ k → lpMinDeg (Pcoef (6 - k)) ≤ k - 2) :
    ∃ C : LaurentSeries (LaurentPolynomial K),
      C ^ 2 = HahnSeries.single (-6 : ℤ) (1 : LaurentPolynomial K) *
          (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial K))
            (PowerSeries.mk fun n => Pcoef (6 - (n : ℤ))) ∧
      v10 C = 3 := by
  obtain ⟨C, hC2, -, hC3, -, -, hCneg⟩ :=
    e19_existence_bounds_s6 Pcoef hPsupp hPneg hq0 hP21 hP1m1
  refine ⟨C, hC2, ?_⟩
  apply v10_of_coeff C
  · rw [hC3]
    exact (isUnit_T 1).ne_zero
  · exact hCneg

/-! ## §7. Tilde-series existence (E20).

Given the tilde polynomial coefficients (`Ptcoef`, top coefficient `C3²`),
`exists_sqrt_series` gives `Ct` with `Ct² = Pt`, `Ct.coeff (-3) = C3`; `Ct ≠ 0`
(because `C3 ≠ 0`), so `Cti := Ct⁻¹` (field inverse, since
`LaurentSeries (RatFunc K)` is a field) satisfies `Ct * Cti = 1`; and `Ft` is
defined as the difference `Qtilde - (Ct³ + lam' * Cti)`, so the Q̃-expansion
holds by definition. The paper's sharper claim (`Ft` has `v10 = -4`,
`lam' = lam - α₁²/3 + …`) is NOT proved here. -/

/-- Tilde-series existence (E20, KERNEL modulo the `Ptcoef` data):
    `Ct² = Pt`, `Ct * Cti = 1`, `Qtilde = Ct³ + lam' * Cti + Ft`,
    `Ct.coeff (-3) = C3`, with the `recDiag` coefficient data for `Ct`. -/
theorem exists_tilde (Ptcoef : ℤ → RatFunc K) (C3 : RatFunc K) (hC3 : C3 ≠ 0)
    (hPsupp : ∀ n : ℤ, 6 < n → Ptcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Ptcoef n = 0)
    (hq0 : Ptcoef 6 = C3 ^ 2) (lam' : RatFunc K)
    (Qtilde : LaurentSeries (RatFunc K)) :
    ∃ Ct Cti Ft : LaurentSeries (RatFunc K),
      Ct ^ 2 = HahnSeries.single (-6 : ℤ) (1 : RatFunc K) *
          (HahnSeries.ofPowerSeries ℤ (RatFunc K))
            (PowerSeries.mk fun n => Ptcoef (6 - (n : ℤ))) ∧
      (∀ k : ℕ, Ct.coeff ((k : ℤ) - 3) =
        recDiag C3 (2 * C3)⁻¹ (fun n => Ptcoef (6 - (n : ℤ))) k) ∧
      Ct * Cti = 1 ∧
      Qtilde = Ct ^ 3 + HahnSeries.C lam' * Cti + Ft ∧
      Ct.coeff (-3) = C3 := by
  have h2C3 : (2 * C3) * (2 * C3)⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero (by norm_num : (2 : RatFunc K) ≠ 0) hC3)
  obtain ⟨Ct, hCt2, hCtcoeff, hCt3, -⟩ :=
    exists_sqrt_series C3 (2 * C3)⁻¹ h2C3 Ptcoef hPsupp hPneg hq0
  have hCtne : Ct ≠ 0 := by
    intro h0
    apply hC3
    rw [← hCt3, h0]
    simp
  refine ⟨Ct, Ct⁻¹, Qtilde - (Ct ^ 3 + HahnSeries.C lam' * Ct⁻¹), hCt2, hCtcoeff,
    mul_inv_cancel₀ hCtne, by abel, hCt3⟩

/-! ## §8. Assembly interface.

`C7AssemblyPremises` lives in Leg D's file (not importable here), so the
discharge is stated as standalone propositions with the same content; the
mapping is documented in the report and log:
- `laurent_series_discharge_s6` discharges the E19 existence + bounds + `v10`
  + leading term (the `laurent_series` premise of `C7AssemblyPremises`).
- `tilde_discharge` discharges the E20 tilde-series premise.
- `bracket_reduction_discharge` discharges the E23 bracket-reduction premise
  (CONDITIONAL on `hdeg`, as in `e23_series_reduction`).
- `f_discharge` discharges the F-existence premise over `RatFunc K`
  (CONDITIONAL on `GGV1Inputs`, as in `exists_F`); `f_discharge_lp_s6` is the
  §6 (LP K) analogue, CONDITIONAL on `GGV1InputsLp` and on the unit `u`
  (the unit is supplied by `isUnit_of_coeff` from the leading coefficient). -/

/-- A series is a unit if its leading coefficient (at t-exponent `-3`) is a
    unit and nothing lies below `-3` (KERNEL, via `HahnSeries.isUnit_iff`). -/
theorem isUnit_of_coeff {R : Type*} [CommRing R] [IsDomain R]
    (C : LaurentSeries R) (h3 : IsUnit (C.coeff (-3)))
    (hlt : ∀ m : ℤ, m < -3 → C.coeff m = 0) : IsUnit C := by
  rw [HahnSeries.isUnit_iff]
  have hCne : C ≠ 0 := by
    intro h0
    rw [h0] at h3
    simp at h3
  have hord : C.order = -3 := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero h3.ne_zero
    · by_contra hlt2
      push_neg at hlt2
      have hne : C.coeff (C.order) ≠ 0 := by
        intro h0
        rw [HahnSeries.coeff_order_eq_zero] at h0
        exact hCne h0
      exact hne (hlt _ hlt2)
  have hx : C.orderTop ≠ ⊤ := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hCne, hord]
    simp
  have hlc : C.leadingCoeff = C.coeff (-3) := by
    have htop' : C.orderTop = ↑(-3 : ℤ) := by
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hCne, hord]
    have htop : C.orderTop.untop hx = -3 := (WithTop.untop_eq_iff hx).mpr htop'
    rw [← HahnSeries.coeff_untop_eq_leadingCoeff hx, htop]
  rw [hlc]
  exact h3

/-- E19 discharge (KERNEL): the series `C` with `C² = P`, `C_{-3} = y`, the
    (b_k)/(c_k) bounds, no coefficients below `-3`, `v10 C = 3`, and the
    leading term `x³y` (i.e. `C - mono 3 1 1` has no coefficient at or below
    t-exponent `-3`). -/
theorem laurent_series_discharge_s6 (Pcoef : ℤ → LaurentPolynomial K)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = (T 1 : LaurentPolynomial K) ^ 2)
    (hP21 : ∀ k : ℤ, 1 ≤ k → lpMaxDeg (Pcoef (6 - k)) ≤ 2 + 2 * k)
    (hP1m1 : ∀ k : ℤ, 1 ≤ k → lpMinDeg (Pcoef (6 - k)) ≤ k - 2) :
    ∃ C : LaurentSeries (LaurentPolynomial K),
      C ^ 2 = HahnSeries.single (-6 : ℤ) (1 : LaurentPolynomial K) *
          (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial K))
            (PowerSeries.mk fun n => Pcoef (6 - (n : ℤ))) ∧
      C.coeff (-3) = T 1 ∧
      (∀ n : ℕ, lpMaxDeg (C.coeff ((n : ℤ) - 3)) ≤ 1 + 2 * (n : ℤ)) ∧
      (∀ n : ℕ, lpMinDeg (C.coeff ((n : ℤ) - 3)) ≤ (n : ℤ) - 1) ∧
      (∀ m : ℤ, m < -3 → C.coeff m = 0) ∧
      v10 C = 3 ∧
      (∀ m : ℤ, m ≤ -3 → (C - mono 3 1 1).coeff m = 0) := by
  obtain ⟨C, hC2, hCcoeff, hC3, hB21, hB1m1, hCneg⟩ :=
    e19_existence_bounds_s6 Pcoef hPsupp hPneg hq0 hP21 hP1m1
  have hv10 : v10 C = 3 := v10_of_coeff C (by rw [hC3]; exact (isUnit_T 1).ne_zero) hCneg
  have hlead : ∀ m : ℤ, m ≤ -3 → (C - mono 3 1 1).coeff m = 0 := by
    intro m hm
    rw [HahnSeries.coeff_sub]
    rcases lt_or_eq_of_le hm with hlt | heq
    · rw [hCneg m hlt, mono_coeff, if_neg (by omega : m ≠ -3), sub_zero]
    · subst heq
      rw [hC3, mono_coeff, if_pos rfl]
      simp
  exact ⟨C, hC2, hC3, hB21, hB1m1, hCneg, hv10, hlead⟩

/-- The tilde polynomial coefficients `Ptcoef n = Pcoef n + (2/3)α₁` at `n = 0`
    (KERNEL): the top coefficient and the support conditions are inherited. -/
theorem tilde_Ptcoef (Pcoef : ℤ → RatFunc K) (α₁ : RatFunc K)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0) :
    ∃ Ptcoef : ℤ → RatFunc K,
      Ptcoef 6 = Pcoef 6 ∧ (∀ n : ℤ, 6 < n → Ptcoef n = 0) ∧
      (∀ n : ℤ, n < 0 → Ptcoef n = 0) ∧
      (∀ n : ℤ, Ptcoef n = Pcoef n + (if n = 0 then (2 / 3 : RatFunc K) * α₁ else 0)) := by
  refine ⟨fun n => Pcoef n + (if n = 0 then (2 / 3 : RatFunc K) * α₁ else 0), ?_, ?_, ?_,
    fun n => rfl⟩
  · simp
  · intro n hn
    show Pcoef n + (if n = 0 then (2 / 3 : RatFunc K) * α₁ else 0) = 0
    rw [if_neg (by omega : n ≠ 0), add_zero]
    exact hPsupp n hn
  · intro n hn
    show Pcoef n + (if n = 0 then (2 / 3 : RatFunc K) * α₁ else 0) = 0
    rw [if_neg (by omega : n ≠ 0), add_zero]
    exact hPneg n hn

/-- E20 discharge (KERNEL modulo the `Ptcoef` construction): the tilde series
    with `Ct² = Pt`, `Ct * Cti = 1`, `Qtilde = Ct³ + lam' * Cti + Ft`. -/
theorem tilde_discharge (Pcoef : ℤ → RatFunc K) (C3 : RatFunc K) (hC3 : C3 ≠ 0)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = C3 ^ 2) (α₁ lam' : RatFunc K)
    (Qtilde : LaurentSeries (RatFunc K)) :
    ∃ Ct Cti Ft : LaurentSeries (RatFunc K),
      Ct ^ 2 = HahnSeries.single (-6 : ℤ) (1 : RatFunc K) *
          (HahnSeries.ofPowerSeries ℤ (RatFunc K))
            (PowerSeries.mk fun n => (Pcoef (6 - (n : ℤ)) +
              (if (6 - (n : ℤ)) = 0 then (2 / 3 : RatFunc K) * α₁ else 0))) ∧
      Ct * Cti = 1 ∧
      Qtilde = Ct ^ 3 + HahnSeries.C lam' * Cti + Ft ∧
      Ct.coeff (-3) = C3 := by
  obtain ⟨Ptcoef, hPt6, hPtSupp, hPtNeg, hPtDef⟩ := tilde_Ptcoef Pcoef α₁ hPsupp hPneg
  obtain ⟨Ct, Cti, Ft, hCt2, -, hCtCi, hQt, hCt3⟩ :=
    exists_tilde Ptcoef C3 hC3 hPtSupp hPtNeg (by rw [hPt6]; exact hq0) lam' Qtilde
  refine ⟨Ct, Cti, Ft, ?_, hCtCi, hQt, hCt3⟩
  rw [hCt2]
  simp only [hPtDef]

/-- E23 discharge (CONDITIONAL on `hdeg`, as in `e23_series_reduction`):
    `[x⁶y², F] = x + R` with `R` having no x-coefficient above degree `1`. -/
theorem bracket_reduction_discharge (F : LaurentSeries (LaurentPolynomial K))
    (hFtop : ∀ m : ℤ, m < 4 → F.coeff m = 0)
    (hdeg : ∀ G : LaurentSeries (LaurentPolynomial K),
      (∀ m : ℤ, m < 4 → G.coeff m = 0) → ∀ m : ℤ, m < -1 →
        (bracket (mono 6 2 1) G).coeff m = 0) :
    ∃ R : LaurentSeries (LaurentPolynomial K),
      bracket (mono 6 2 1) F = mono 1 0 1 + R ∧ ∀ m : ℤ, m < -1 → R.coeff m = 0 :=
  e23_series_reduction F hFtop hdeg

/-- F-existence discharge over `RatFunc K` (CONDITIONAL on `GGV1Inputs`, as in
    `exists_F`), with the `Fpoly` unfolding made explicit. -/
theorem f_discharge (C Q : LaurentSeries (RatFunc K)) (α₂ α₁ α₀ αm1 : RatFunc K)
    (h : GGV1Inputs C Q α₂ α₁ α₀ αm1) :
    ∃ F : LaurentSeries (RatFunc K),
      Q = C ^ 3 + HahnSeries.C α₂ * C ^ 2 + HahnSeries.C α₁ * C + HahnSeries.C α₀ +
        HahnSeries.C αm1 * C⁻¹ + F ∧ v10 F = -4 :=
  exists_F C Q α₂ α₁ α₀ αm1 h

/-- The polynomial part of the Q-expansion over `LaurentPolynomial K`, with the
    inverse of `C` taken through the unit `u` (since `LaurentSeries (LP K)` is
    a ring, not a field). -/
noncomputable def FpolyLp (C : LaurentSeries (LaurentPolynomial K))
    (u : (LaurentSeries (LaurentPolynomial K))ˣ)
    (α₂ α₁ α₀ αm1 : LaurentPolynomial K) : LaurentSeries (LaurentPolynomial K) :=
  C ^ 3 + HahnSeries.C α₂ * C ^ 2 + HahnSeries.C α₁ * C + HahnSeries.C α₀ +
    HahnSeries.C αm1 * ((u⁻¹ : (LaurentSeries (LaurentPolynomial K))ˣ) :
      LaurentSeries (LaurentPolynomial K))

/-- The [GGV1]/[GGV3] inputs for the F-construction over `LaurentPolynomial K`
    (the §6 analogue of `GGV1Inputs`), stated at coefficient level. -/
structure GGV1InputsLp (C Q : LaurentSeries (LaurentPolynomial K))
    (u : (LaurentSeries (LaurentPolynomial K))ˣ)
    (α₂ α₁ α₀ αm1 : LaurentPolynomial K) : Prop where
  cancel : ∀ m : ℤ, m < 4 → (Q - FpolyLp C u α₂ α₁ α₀ αm1).coeff m = 0
  leading : (Q - FpolyLp C u α₂ α₁ α₀ αm1).coeff 4 ≠ 0

/-- F-existence over `LaurentPolynomial K` (CONDITIONAL on `GGV1InputsLp` and
    on the unit `u` with `↑u = C`). -/
theorem exists_F_lp (C Q : LaurentSeries (LaurentPolynomial K))
    (u : (LaurentSeries (LaurentPolynomial K))ˣ)
    (hu : (u : LaurentSeries (LaurentPolynomial K)) = C)
    (α₂ α₁ α₀ αm1 : LaurentPolynomial K)
    (h : GGV1InputsLp C Q u α₂ α₁ α₀ αm1) :
    ∃ F : LaurentSeries (LaurentPolynomial K),
      Q = FpolyLp C u α₂ α₁ α₀ αm1 + F ∧ v10 F = -4 := by
  refine ⟨Q - FpolyLp C u α₂ α₁ α₀ αm1, by abel, ?_⟩
  have hFne : Q - FpolyLp C u α₂ α₁ α₀ αm1 ≠ 0 := by
    intro h0
    apply h.leading
    have hc := congrArg (fun f : LaurentSeries (LaurentPolynomial K) => f.coeff 4) h0
    rw [show (0 : LaurentSeries (LaurentPolynomial K)).coeff 4 = 0 from by simp] at hc
    exact hc
  have hord : (Q - FpolyLp C u α₂ α₁ α₀ αm1).order = 4 := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero h.leading
    · by_contra hlt
      push_neg at hlt
      have hne : (Q - FpolyLp C u α₂ α₁ α₀ αm1).coeff
          ((Q - FpolyLp C u α₂ α₁ α₀ αm1).order) ≠ 0 := by
        intro h0
        rw [HahnSeries.coeff_order_eq_zero] at h0
        exact hFne h0
      exact hne (h.cancel _ hlt)
  show -((Q - FpolyLp C u α₂ α₁ α₀ αm1).order) = -4
  rw [hord]

/-- §6 F-discharge (CONDITIONAL on `GGV1InputsLp`): from the E19 data, the
    series `C` (with `C² = P`, `v10 C = 3`, unit via `isUnit_of_coeff`) and
    the `F` with `v10 F = -4`. -/
theorem f_discharge_lp_s6 (Pcoef : ℤ → LaurentPolynomial K)
    (hPsupp : ∀ n : ℤ, 6 < n → Pcoef n = 0) (hPneg : ∀ n : ℤ, n < 0 → Pcoef n = 0)
    (hq0 : Pcoef 6 = (T 1 : LaurentPolynomial K) ^ 2)
    (hP21 : ∀ k : ℤ, 1 ≤ k → lpMaxDeg (Pcoef (6 - k)) ≤ 2 + 2 * k)
    (hP1m1 : ∀ k : ℤ, 1 ≤ k → lpMinDeg (Pcoef (6 - k)) ≤ k - 2)
    (Q : LaurentSeries (LaurentPolynomial K)) (α₂ α₁ α₀ αm1 : LaurentPolynomial K)
    (h : ∀ (C : LaurentSeries (LaurentPolynomial K))
      (u : (LaurentSeries (LaurentPolynomial K))ˣ),
      (u : LaurentSeries (LaurentPolynomial K)) = C →
      GGV1InputsLp C Q u α₂ α₁ α₀ αm1) :
    ∃ C F : LaurentSeries (LaurentPolynomial K),
      C ^ 2 = HahnSeries.single (-6 : ℤ) (1 : LaurentPolynomial K) *
          (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial K))
            (PowerSeries.mk fun n => Pcoef (6 - (n : ℤ))) ∧
      v10 C = 3 ∧
      ∃ u : (LaurentSeries (LaurentPolynomial K))ˣ,
        (u : LaurentSeries (LaurentPolynomial K)) = C ∧
        Q = FpolyLp C u α₂ α₁ α₀ αm1 + F ∧ v10 F = -4 := by
  obtain ⟨C, hC2, hCcoeff, hC3, -, -, hCneg⟩ :=
    e19_existence_bounds_s6 Pcoef hPsupp hPneg hq0 hP21 hP1m1
  have hCunit : IsUnit C := isUnit_of_coeff C (by rw [hC3]; exact isUnit_T 1) hCneg
  obtain ⟨u, hu⟩ := hCunit
  obtain ⟨F, hQF, hFv10⟩ := exists_F_lp C Q u hu α₂ α₁ α₀ αm1 (h C u hu)
  exact ⟨C, F, hC2, v10_of_coeff C (by rw [hC3]; exact (isUnit_T 1).ne_zero) hCneg,
    u, hu, hQF, hFv10⟩
