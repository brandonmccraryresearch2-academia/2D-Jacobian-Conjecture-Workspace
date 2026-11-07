import Mathlib
import TwoDicritical.E1Obstruction

/-!
# The `E₁` step: Theorem `thm:e1` is false as stated, and its intended conclusion holds

**The order condition.** `E₁` is the blow-up of `[1:0:0]` (line at infinity `Z = 0`, `x = X/Z`, `y = Y/Z`). In the
chart `s = y/x = s₁`, `t = 1/x = s₁t₁` of `e1_solitary.py`, `x^i y^j = s₁^(−i) t₁^(−i−j)`, so
`ν_{E₁}(x^i y^j) = −i`: the condition `ν_{E₁} ≥ −2` says **`x`-degree at most 2**. The script indexes its unknowns
`p[J,K]` by `X^(d−J−K) Y^J Z^K`, that is, by the affine monomial `x^(d−J−K) y^J`. Read as `x^J y^K`, its condition
`J + K ≥ d − 2` becomes "total degree at least 2" (`e1_keller_search.py`, `noLowTerms` of `E1Obstruction.lean`). At
`d = 4` both sets have 12 monomials, which hid the mix-up; they differ (`x`, `y`, `1` versus `x³`, `x³y`, `x⁴`).
Checked in `lean/check_e1_index.py`.

**The counterexample** (`thm_e1_false`). `P = (x + y²)² + y` and `Q = P + x + y²` have degree 4, `x`-degree 2 and
`x²`-coefficient 1, so both lie in the paper's `E₁` `m = 2` open subset at `d = 4` (`E1Open4`: `ν_{E₁} = −2` and
`C(t₁) = t₁²` of exact degree 2), and `[P, Q] = −1`. So "`[P,Q]` is never a nonzero constant" is false. `E₁` is still
not dicritical for this pair: `P/Q` restricts to `C_P/C_Q = 1` on it. `E1Obstruction.lean` remains a true theorem
about polynomials without terms of degree below 2, a different set: `P` contains `y` (`e1P_not_noLowTerms`).

**The corrected step** (`e1_lead_proportional`). Write `K[x,y]` as polynomials in `x` over `K[y]`
(`Polynomial (Polynomial K)`, the outer variable is `x`). If `P` and `Q` have `x`-degree at most `n ≥ 1` and their
Jacobian is constant, then the coefficients `A`, `D ∈ K[y]` of `xⁿ` are proportional: the `x^(2n−1)`-coefficient of
`[P,Q]` is `n·(A·D' − A'·D)` (`jac2_coeff_top`), and a vanishing Wronskian forces proportionality in characteristic 0
(`eq_C_mul_of_wronskian_eq_zero`). On `E₁`, `P/Q` restricts to `A(1/t₁)/D(1/t₁)` when both have `x`-degree `n`, and to
`0` or `∞` otherwise (chart computation, `lean/check_e1_index.py`). So **`E₁` is not dicritical for any Keller map, of
any order `m`**. This is the conclusion `thm:e1` was meant to give, for all `m`, not only `m = 2`.

What is not formalized: the chart computation (the order condition and the restriction to `E₁`), which is executed in
`lean/check_e1_index.py`.
-/

namespace TwoDicritical

section Counterexample

open MvPolynomial

variable {K : Type*} [Field K]

/-- `P = x² + 2xy² + y⁴ + y = (x + y²)² + y`, with `x = X 0`, `y = X 1`. -/
noncomputable def e1P : MvPolynomial (Fin 2) K :=
  monomial (Finsupp.single 0 2) 1 + monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 2 +
    monomial (Finsupp.single 1 4) 1 + monomial (Finsupp.single 1 1) 1

/-- `Q = P + x + y²`. -/
noncomputable def e1Q : MvPolynomial (Fin 2) K :=
  e1P + monomial (Finsupp.single 0 1) 1 + monomial (Finsupp.single 1 2) 1

theorem e1P_eq : (e1P : MvPolynomial (Fin 2) K) = (X 0 + X 1 ^ 2) ^ 2 + X 1 := by
  simp only [e1P, monomial_single_add, ← C_mul_X_pow_eq_monomial, pow_one, map_one, one_mul]
  rw [show (C 2 : MvPolynomial (Fin 2) K) = 2 from map_ofNat C 2]
  ring

theorem e1Q_eq : (e1Q : MvPolynomial (Fin 2) K) = (X 0 + X 1 ^ 2) ^ 2 + X 1 + X 0 + X 1 ^ 2 := by
  rw [e1Q, e1P_eq, ← X_pow_eq_monomial, ← X_pow_eq_monomial, pow_one]

/-- The paper's `E₁` `m = 2` open subset at `d = 4`, in affine terms: degree at most 4, `x`-degree at most 2
(`ν_{E₁} ≥ −2`), and a nonzero `x²`-coefficient (`ν_{E₁} = −2` and `C(t₁)` of exact degree 2). -/
def E1Open4 (P : MvPolynomial (Fin 2) K) : Prop :=
  (∀ m ∈ P.support, m 0 + m 1 ≤ 4 ∧ m 0 ≤ 2) ∧ P.coeff (Finsupp.single 0 2) ≠ 0

/-- The exponents of `e1Q` (and of `e1P`). -/
theorem support_e1Q : (e1Q : MvPolynomial (Fin 2) K).support ⊆
    {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 2, Finsupp.single 1 4, Finsupp.single 1 1,
      Finsupp.single 0 1, Finsupp.single 1 2} := by
  intro m hm
  simp only [e1Q, e1P] at hm
  repeat rw [Finset.mem_insert]
  rw [Finset.mem_singleton]
  have hs := fun (s : Fin 2 →₀ ℕ) (a : K) => support_monomial_subset (s := s) (a := a)
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · rcases Finset.mem_union.mp (support_add h) with h | h
    · rcases Finset.mem_union.mp (support_add h) with h | h
      · rcases Finset.mem_union.mp (support_add h) with h | h
        · rcases Finset.mem_union.mp (support_add h) with h | h
          · exact Or.inl (Finset.mem_singleton.mp (hs _ _ h))
          · exact Or.inr (Or.inl (Finset.mem_singleton.mp (hs _ _ h)))
        · exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp (hs _ _ h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp (hs _ _ h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp (hs _ _ h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp (hs _ _ h))))))

theorem support_e1P : (e1P : MvPolynomial (Fin 2) K).support ⊆
    {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 2, Finsupp.single 1 4, Finsupp.single 1 1} := by
  intro m hm
  simp only [e1P] at hm
  repeat rw [Finset.mem_insert]
  rw [Finset.mem_singleton]
  have hs := fun (s : Fin 2 →₀ ℕ) (a : K) => support_monomial_subset (s := s) (a := a)
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · rcases Finset.mem_union.mp (support_add h) with h | h
    · rcases Finset.mem_union.mp (support_add h) with h | h
      · exact Or.inl (Finset.mem_singleton.mp (hs _ _ h))
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp (hs _ _ h)))
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp (hs _ _ h))))
  · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp (hs _ _ h))))

/-- Distinct exponents, compared at the coordinates `0` and `1`. -/
theorem fs_ne {a b : Fin 2 →₀ ℕ} (h : a 0 ≠ b 0 ∨ a 1 ≠ b 1) : a ≠ b := by
  rintro rfl; rcases h with h | h <;> exact h rfl

theorem coeff_e1P_x2 : (e1P : MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 2) = 1 := by
  have h1 : (Finsupp.single 0 1 + Finsupp.single 1 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := fs_ne (by simp)
  have h2 : (Finsupp.single 1 4 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := fs_ne (by simp)
  have h3 : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := fs_ne (by simp)
  simp [e1P, coeff_monomial, h1, h2, h3]

theorem coeff_e1P_y : (e1P : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 1) = 1 := by
  have h0 : (Finsupp.single 0 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fs_ne (by simp)
  have h1 : (Finsupp.single 0 1 + Finsupp.single 1 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fs_ne (by simp)
  have h2 : (Finsupp.single 1 4 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fs_ne (by simp)
  simp [e1P, coeff_monomial, h0, h1, h2]

theorem coeff_e1Q_x2 : (e1Q : MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 2) = 1 := by
  have h4 : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := fs_ne (by simp)
  have h5 : (Finsupp.single 1 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := fs_ne (by simp)
  simp [e1Q, coeff_e1P_x2, coeff_monomial, h4, h5]

theorem coeff_e1Q_y : (e1Q : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 1) = 1 := by
  have h4 : (Finsupp.single 0 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fs_ne (by simp)
  have h5 : (Finsupp.single 1 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := fs_ne (by simp)
  simp [e1Q, coeff_e1P_y, coeff_monomial, h4, h5]

theorem e1Open4_e1P : E1Open4 (e1P : MvPolynomial (Fin 2) K) := by
  refine ⟨fun m hm => ?_, by rw [coeff_e1P_x2]; exact one_ne_zero⟩
  have h := support_e1P hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem e1Open4_e1Q : E1Open4 (e1Q : MvPolynomial (Fin 2) K) := by
  refine ⟨fun m hm => ?_, by rw [coeff_e1Q_x2]; exact one_ne_zero⟩
  have h := support_e1Q hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- `[P, Q] = −1`. -/
theorem jacobian_e1 : jacobian (e1P : MvPolynomial (Fin 2) K) e1Q = C (-1) := by
  rw [jacobian, e1Q_eq, e1P_eq]
  simp only [map_add, Derivation.leibniz_pow, pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, nsmul_eq_mul, map_neg, map_one]
  ring

/-- **Theorem `thm:e1` is false as stated**: a pair in the `E₁` `m = 2` open subset at `d = 4` with `[P,Q] = −1`. -/
theorem thm_e1_false :
    E1Open4 (e1P : MvPolynomial (Fin 2) K) ∧ E1Open4 (e1Q : MvPolynomial (Fin 2) K) ∧
      IsKeller (e1P : MvPolynomial (Fin 2) K) e1Q :=
  ⟨e1Open4_e1P, e1Open4_e1Q, ⟨-1, neg_ne_zero.mpr one_ne_zero, jacobian_e1⟩⟩

/-- `E1Obstruction.lean`'s hypothesis is not the `E₁` condition: `P` contains `y`. -/
theorem e1P_not_noLowTerms : ¬ noLowTerms (e1P : MvPolynomial (Fin 2) K) := by
  intro h
  have hy : Finsupp.single (1 : Fin 2) 1 ∈ (e1P : MvPolynomial (Fin 2) K).support := by
    rw [mem_support_iff, coeff_e1P_y]; exact one_ne_zero
  have := h _ hy
  simp [totDeg] at this

end Counterexample

section Corrected

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- If `B·D' = B'·D` with `B, D ≠ 0`, then `B` and `D` have the same degree (characteristic 0). -/
theorem natDegree_eq_of_wronskian {B D : K[X]} (hB : B ≠ 0) (hD : D ≠ 0)
    (h : B * derivative D = derivative B * D) : B.natDegree = D.natDegree := by
  by_contra hmn
  rcases Nat.eq_zero_or_pos D.natDegree with hn | hn
  · -- `D` constant: then `B' = 0`, so `B` is constant too
    have hD' : derivative D = 0 := derivative_of_natDegree_zero hn
    rw [hD', mul_zero] at h
    have hB' : derivative B = 0 := (mul_eq_zero.mp h.symm).resolve_right hD
    exact hmn ((derivative_eq_zero.mp hB').trans hn.symm)
  rcases Nat.eq_zero_or_pos B.natDegree with hm | hm
  · have hB' : derivative B = 0 := derivative_of_natDegree_zero hm
    rw [hB', zero_mul] at h
    have hD' : derivative D = 0 := (mul_eq_zero.mp h).resolve_left hB
    exact hmn (hm.trans (derivative_eq_zero.mp hD').symm)
  -- both positive: compare the coefficients of `X^(m + n − 1)`
  set m := B.natDegree with hm_def
  set n := D.natDegree with hn_def
  have hdD : (derivative D).natDegree ≤ n - 1 := natDegree_derivative_le D
  have hdB : (derivative B).natDegree ≤ m - 1 := natDegree_derivative_le B
  have e1 : (B * derivative D).coeff (m + (n - 1)) = B.leadingCoeff * (D.leadingCoeff * n) := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl hdD, coeff_derivative, show n - 1 + 1 = n by omega]
    have : ((n - 1 : ℕ) : K) + 1 = n := by rw [← Nat.cast_succ]; congr 1; omega
    rw [this]; rfl
  have e2 : (derivative B * D).coeff ((m - 1) + n) = B.leadingCoeff * m * D.leadingCoeff := by
    rw [coeff_mul_add_eq_of_natDegree_le hdB le_rfl, coeff_derivative, show m - 1 + 1 = m by omega]
    have : ((m - 1 : ℕ) : K) + 1 = m := by rw [← Nat.cast_succ]; congr 1; omega
    rw [this]; rfl
  have hidx : m + (n - 1) = (m - 1) + n := by omega
  rw [h, hidx, e2] at e1
  have hlc : B.leadingCoeff * D.leadingCoeff ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hB) (leadingCoeff_ne_zero.mpr hD)
  have hcast : ((m : ℕ) : K) = (n : K) := by
    have : B.leadingCoeff * D.leadingCoeff * ((m : K) - n) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hlc)
  exact hmn (Nat.cast_injective hcast)

/-- **Vanishing Wronskian (characteristic 0).** If `A·D' = A'·D` and `D ≠ 0`, then `A = r·D` for some `r ∈ K`. -/
theorem eq_C_mul_of_wronskian {A D : K[X]} (hD : D ≠ 0) (h : A * derivative D = derivative A * D) :
    ∃ r : K, A = C r * D := by
  by_cases hA : A = 0
  · exact ⟨0, by simp [hA]⟩
  have hdeg := natDegree_eq_of_wronskian hA hD h
  refine ⟨A.leadingCoeff / D.leadingCoeff, ?_⟩
  by_contra hne
  set r := A.leadingCoeff / D.leadingCoeff with hr
  have hB : A - C r * D ≠ 0 := sub_ne_zero.mpr hne
  have hBw : (A - C r * D) * derivative D = derivative (A - C r * D) * D := by
    rw [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
    linear_combination h
  have hBdeg := natDegree_eq_of_wronskian hB hD hBw
  have hcoeff : (A - C r * D).coeff D.natDegree = 0 := by
    rw [coeff_sub, coeff_C_mul, ← hdeg]
    have hD0 : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hD
    change A.leadingCoeff - r * D.coeff A.natDegree = 0
    rw [hdeg]
    change A.leadingCoeff - r * D.leadingCoeff = 0
    rw [hr, div_mul_cancel₀ _ hD0, sub_self]
  have hlc := leadingCoeff_ne_zero.mpr hB
  rw [leadingCoeff, hBdeg] at hlc
  exact hlc hcoeff

/-- `∂/∂y` on `K[y][x]`: the derivative applied to each coefficient. -/
noncomputable def dY (P : Polynomial (Polynomial K)) : Polynomial (Polynomial K) :=
  P.sum fun n a => monomial n (derivative a)

omit [CharZero K] in
theorem coeff_dY (P : Polynomial (Polynomial K)) (k : ℕ) : (dY P).coeff k = derivative (P.coeff k) := by
  rw [dY, coeff_sum]
  simp only [coeff_monomial]
  rw [Polynomial.sum_def, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [notMem_support_iff.mp hk, derivative_zero]

/-- The Jacobian `[P,Q] = P_x Q_y − P_y Q_x` on `K[y][x]` (outer variable `x`). -/
noncomputable def jac2 (P Q : Polynomial (Polynomial K)) : Polynomial (Polynomial K) :=
  derivative P * dY Q - dY P * derivative Q

omit [CharZero K] in
theorem natDegree_dY_le (P : Polynomial (Polynomial K)) {n : ℕ} (hP : P.natDegree ≤ n) : (dY P).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_dY, coeff_eq_zero_of_natDegree_lt (by omega), derivative_zero]

omit [CharZero K] in
/-- **The top coefficient.** For `x`-degrees at most `n ≥ 1`, the `x^(2n−1)`-coefficient of `[P,Q]` is
`n·(A·D' − A'·D)`, where `A`, `D` are the `xⁿ`-coefficients. -/
theorem jac2_coeff_top (P Q : Polynomial (Polynomial K)) (n : ℕ) (hn : 1 ≤ n)
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n) :
    (jac2 P Q).coeff (2 * n - 1) =
      (n : Polynomial K) * (P.coeff n * derivative (Q.coeff n) - derivative (P.coeff n) * Q.coeff n) := by
  have hdP : (derivative P).natDegree ≤ n - 1 := (natDegree_derivative_le P).trans (by omega)
  have hdQ : (derivative Q).natDegree ≤ n - 1 := (natDegree_derivative_le Q).trans (by omega)
  have hcast : ((n - 1 : ℕ) : Polynomial K) + 1 = n := by rw [← Nat.cast_succ]; congr 1; omega
  have e1 : (derivative P * dY Q).coeff (2 * n - 1) = P.coeff n * n * derivative (Q.coeff n) := by
    rw [show 2 * n - 1 = (n - 1) + n by omega, coeff_mul_add_eq_of_natDegree_le hdP (natDegree_dY_le Q hQ),
      coeff_derivative, coeff_dY, show n - 1 + 1 = n by omega, hcast]
  have e2 : (dY P * derivative Q).coeff (2 * n - 1) = derivative (P.coeff n) * (Q.coeff n * n) := by
    rw [show 2 * n - 1 = n + (n - 1) by omega, coeff_mul_add_eq_of_natDegree_le (natDegree_dY_le P hP) hdQ,
      coeff_derivative, coeff_dY, show n - 1 + 1 = n by omega, hcast]
  rw [jac2, coeff_sub, e1, e2]
  ring

/-- **The `E₁` step, corrected.** If `P` and `Q` have `x`-degree at most `n ≥ 1` and a constant Jacobian, then the
`xⁿ`-coefficient of `P` is a constant multiple of that of `Q`, or the latter vanishes. Hence `P/Q` is constant on
`E₁`: `E₁` is not dicritical for a Keller map. -/
theorem e1_lead_proportional (P Q : Polynomial (Polynomial K)) (n : ℕ) (hn : 1 ≤ n)
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n) (c : K) (hJ : jac2 P Q = C (C c)) :
    Q.coeff n = 0 ∨ ∃ r : K, P.coeff n = C r * Q.coeff n := by
  have htop := jac2_coeff_top P Q n hn hP hQ
  have h2n : 2 * n - 1 ≠ 0 := by omega
  rw [hJ, coeff_C, ite_eq_right h2n] at htop
  have hn0 : (n : Polynomial K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hW : P.coeff n * derivative (Q.coeff n) = derivative (P.coeff n) * Q.coeff n :=
    sub_eq_zero.mp ((mul_eq_zero.mp htop.symm).resolve_left hn0)
  by_cases hD : Q.coeff n = 0
  · exact Or.inl hD
  · exact Or.inr (eq_C_mul_of_wronskian hD hW)

omit [CharZero K] in
/-- If both `x`-degrees are 0, the Jacobian vanishes: such a pair is not Keller. -/
theorem jac2_eq_zero_of_natDegree_zero (P Q : Polynomial (Polynomial K)) (hP : P.natDegree = 0)
    (hQ : Q.natDegree = 0) : jac2 P Q = 0 := by
  rw [jac2, derivative_of_natDegree_zero hP, derivative_of_natDegree_zero hQ, zero_mul, mul_zero, sub_zero]

end Corrected

end TwoDicritical
