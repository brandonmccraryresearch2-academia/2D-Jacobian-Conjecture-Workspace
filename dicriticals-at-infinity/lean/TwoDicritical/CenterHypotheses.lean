import TwoDicritical.BridgeCollapse

/-!
# The center hypotheses cannot be dropped from `bridge_collapse`, a theorem about equations

`bridge_collapse` and `bridge_jacobian_eq_zero` assume `a₃ ≠ 0`, `a₄ ≠ 0` and `a₃ ≠ a₄`, as the paper's §3.1 does
("two distinct centers a₃ ≠ a₄ (both nonzero)"). This file shows that none of the three can be dropped from the
theorem about the equations `bridgeEq`.

**What this means geometrically** (corrected on 2026-10-13, after an outside referee's report on PR #19; executed in
`check_satellite.py`). The paper's pullback (eq:bridge-pullback) is `Sʰ(1, b, b²(a + ã b))`: the chart at the point
`w₂ = a` of the second exceptional curve `E₂` over `[1:0:0]`, where `w₂ = x/y²`.
* For `a ≠ 0` the point is free. The normalizing factor `Zᵈ` becomes `b^(2d)` times a unit, and `ord_b S_a ≥ 2d − 1`
  says `ν ≥ −1` on the divisor over `a`.
* The point `a = 0` is where `E₂` meets the line at infinity, a satellite point. There `Zᵈ` becomes `ãᵈ b^(3d)`, and
  the same threshold says `ν ≥ −(d + 1)`. That condition weakens as the bound `d` grows, so it is not a property of
  the pencil.

So a center at `0` in these equations is not a bridge center. The witness below has degree 2 and satisfies the
equations only for `d ≥ 3`. Over `a = 0` its `P/Q` has a pole, and its only dicritical at infinity lies over the free
point `a₄`. The hypothesis `a ≠ 0` marks where the formula applies; it does not mark a missing argument that a center
cannot sit at `0`. What the paper does not treat are dicriticals over the satellite points `a = 0` and `a = ∞` of
`E₂`, and over deeper ones. `OneCenter.lean` gives what the equations say with one center, and with `d` read as the
exact degree.

The witness is `x − c·y²` (coefficient vector `pAuto c`). At weight `W = 2` its bridge equation at a center `a` is
`a^(d−2)·(a − c)` (`bridgeEq_two_pAuto`); at every other weight it has no variable. So the bridge conditions hold
whenever both centers satisfy `a^(d−2)·(a − c) = 0` (`bridgeConditions_pAuto`):

* `a₃ = 0`, `c = a₄`, `d ≥ 3` (`0^(d−2) = 0`): `a₃ ≠ 0` is needed in the formal theorem (and `a₄ ≠ 0`, by
  symmetry);
* `a₃ = a₄ = c`, `d ≥ 2`: `a₃ ≠ a₄` is needed.

In each case the coefficient of `x` is `1`, so `bridge_collapse` fails without the hypothesis
(`bridge_collapse_needs_ne_zero`, `bridge_collapse_needs_ne`), and with `Q = y` the pair `(x − c·y², y)`, a polynomial
automorphism with Jacobian `1` (`jacobian_auto`), satisfies every other hypothesis of `bridge_jacobian_eq_zero`
(`bridge_jacobian_needs_ne_zero`). At `d = 2` a center at `0` is harmless (`0^0 = 1`).
-/

open Finset

namespace TwoDicritical

variable {K : Type*} [Field K]

/-- The coefficients of `x − c·y²`: `p (J, L)` is the coefficient of `x^J y^L`. -/
def pAuto (c : K) : ℕ × ℕ → K := fun JL => if JL = (1, 0) then 1 else if JL = (0, 2) then -c else 0

/-- The weight-2 bridge equation of `x − c·y²` at a center `a`. -/
theorem bridgeEq_two_pAuto (d : ℕ) (hd : 2 ≤ d) (c a : K) :
    bridgeEq d 2 0 a (pAuto c) = a ^ (d - 2) * (a - c) := by
  have hIco : Ico (2 - d) (2 / 2 + 1) = {0, 1} := by
    have : 2 - d = 0 := by omega
    rw [this]; decide
  unfold bridgeEq
  rw [hIco, Finset.sum_pair (by norm_num)]
  have h1 : pAuto c (0, 2 - 2 * 0) = -c := by simp [pAuto]
  have h2 : pAuto c (1, 2 - 2 * 1) = 1 := by simp [pAuto]
  rw [h1, h2]
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [show d + 0 - 2 - 0 = d - 2 by omega, show d + 1 - 2 - 0 = d - 2 + 1 by omega, pow_succ]
  ring

/-- At every weight other than 2, `x − c·y²` has no variable, so its bridge equations vanish. -/
theorem bridgeEq_pAuto_of_ne_two (d W i : ℕ) (hW : W ≠ 2) (c a : K) : bridgeEq d W i a (pAuto c) = 0 := by
  unfold bridgeEq
  refine Finset.sum_eq_zero (fun J hJ => ?_)
  rw [Finset.mem_Ico] at hJ
  have hz : pAuto c (J, W - 2 * J) = 0 := by
    unfold pAuto
    split_ifs with h1 h2
    · exfalso; simp only [Prod.mk.injEq] at h1; omega
    · exfalso; simp only [Prod.mk.injEq] at h2; omega
    · rfl
  rw [hz, zero_mul, zero_mul]

/-- The bridge conditions for `x − c·y²`: they hold as soon as `a^(d−2)·(a − c) = 0` at both centers. -/
theorem bridgeConditions_pAuto (d : ℕ) (hd : 2 ≤ d) (a₃ a₄ c : K) (h₃ : a₃ ^ (d - 2) * (a₃ - c) = 0)
    (h₄ : a₄ ^ (d - 2) * (a₄ - c) = 0) : BridgeConditions d a₃ a₄ (pAuto c) := by
  intro W i hW hi
  by_cases hW2 : W = 2
  · subst hW2
    obtain rfl : i = 0 := by omega
    rw [bridgeEq_two_pAuto d hd, bridgeEq_two_pAuto d hd]
    exact ⟨h₃, h₄⟩
  · exact ⟨bridgeEq_pAuto_of_ne_two d W i hW2 c a₃, bridgeEq_pAuto_of_ne_two d W i hW2 c a₄⟩

/-- A center at `0` (`d ≥ 3`): the bridge conditions at the centers `0` and `a₄` hold for `x − a₄·y²`. -/
theorem bridgeConditions_zero_center (d : ℕ) (hd : 3 ≤ d) (a₄ : K) : BridgeConditions d 0 a₄ (pAuto a₄) :=
  bridgeConditions_pAuto d (by omega) 0 a₄ a₄ (by rw [zero_pow (by omega), zero_mul]) (by rw [sub_self, mul_zero])

/-- Equal centers (`d ≥ 2`): the bridge conditions at `a` and `a` hold for `x − a·y²`. -/
theorem bridgeConditions_equal_centers (d : ℕ) (hd : 2 ≤ d) (a : K) : BridgeConditions d a a (pAuto a) :=
  bridgeConditions_pAuto d hd a a a (by rw [sub_self, mul_zero]) (by rw [sub_self, mul_zero])

/-- `bridge_collapse` without `a₃ ≠ 0` is false (`d = 3`, centers `0` and `1`, over `ℚ`). -/
theorem bridge_collapse_needs_ne_zero :
    ¬ ∀ (d : ℕ) (a₃ a₄ : ℚ), a₄ ≠ 0 → a₃ ≠ a₄ → ∀ p : ℕ × ℕ → ℚ, BridgeConditions d a₃ a₄ p →
      ∀ J L : ℕ, J + L ≤ d → 2 ≤ 2 * J + L → p (J, L) = 0 := by
  intro h
  have := h 3 0 1 one_ne_zero (by norm_num) (pAuto 1) (bridgeConditions_zero_center 3 le_rfl 1) 1 0
    (by norm_num) (by norm_num)
  simp [pAuto] at this

/-- `bridge_collapse` without `a₃ ≠ a₄` is false (`d = 2`, both centers `1`, over `ℚ`). -/
theorem bridge_collapse_needs_ne :
    ¬ ∀ (d : ℕ) (a₃ a₄ : ℚ), a₃ ≠ 0 → a₄ ≠ 0 → ∀ p : ℕ × ℕ → ℚ, BridgeConditions d a₃ a₄ p →
      ∀ J L : ℕ, J + L ≤ d → 2 ≤ 2 * J + L → p (J, L) = 0 := by
  intro h
  have := h 2 1 1 one_ne_zero one_ne_zero (pAuto 1) (bridgeConditions_equal_centers 2 le_rfl 1) 1 0
    (by norm_num) (by norm_num)
  simp [pAuto] at this

/-! ### The polynomial level: `(x − c·y², y)` is a Keller pair in the bridge -/

open MvPolynomial in
/-- The polynomial `x − c·y²`. -/
noncomputable def polyAuto (c : K) : MvPolynomial (Fin 2) K := X 0 - C c * X 1 ^ 2

/-- Every monomial on `Fin 2` is `x^(m 0) y^(m 1)`. -/
theorem mono_eq (m : Fin 2 →₀ ℕ) : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
  ext i; fin_cases i <;> simp

/-- `x^n` is the monomial `x^J y^L` iff `J = n` and `L = 0`. -/
theorem single_x_eq_iff (n J L : ℕ) :
    Finsupp.single (0 : Fin 2) n = Finsupp.single 0 J + Finsupp.single 1 L ↔ J = n ∧ L = 0 := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h0 h1
    simp at h0 h1
    omega
  · rintro ⟨rfl, rfl⟩
    simp

/-- `y^n` is the monomial `x^J y^L` iff `J = 0` and `L = n`. -/
theorem single_y_eq_iff (n J L : ℕ) :
    Finsupp.single (1 : Fin 2) n = Finsupp.single 0 J + Finsupp.single 1 L ↔ J = 0 ∧ L = n := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h0 h1
    simp at h0 h1
    omega
  · rintro ⟨rfl, rfl⟩
    simp

/-- The coefficients of `x − c·y²` are `pAuto c`. -/
theorem coeff_polyAuto (c : K) (J L : ℕ) :
    (polyAuto c).coeff (Finsupp.single 0 J + Finsupp.single 1 L) = pAuto c (J, L) := by
  unfold polyAuto pAuto
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_X_pow]
  simp only [single_x_eq_iff, single_y_eq_iff, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The coefficients of `y`. -/
theorem coeff_y (J L : ℕ) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 J + Finsupp.single 1 L) =
      if (J, L) = (0, 1) then 1 else 0 := by
  rw [MvPolynomial.coeff_X]
  simp only [single_y_eq_iff, Prod.mk.injEq]

/-- `y` satisfies every bridge condition (it has weight 1). -/
theorem bridgeConditions_y (d : ℕ) (a₃ a₄ : K) :
    BridgeConditions d a₃ a₄ (fun JL => (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) := by
  intro W i hW hi
  have hz : ∀ (a : K), bridgeEq d W i a (fun JL => (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) = 0 := by
    intro a
    unfold bridgeEq
    refine Finset.sum_eq_zero (fun J hJ => ?_)
    rw [Finset.mem_Ico] at hJ
    simp only
    rw [coeff_y, ite_eq_right (by simp only [Prod.mk.injEq]; omega), zero_mul, zero_mul]
  exact ⟨hz a₃, hz a₄⟩

open MvPolynomial in
/-- The Jacobian of `(x − c·y², y)` is `1`. -/
theorem jacobian_auto (c : K) :
    pderiv 0 (polyAuto c) * pderiv 1 (X 1) - pderiv 1 (polyAuto c) * pderiv 0 (X 1 : MvPolynomial (Fin 2) K) = 1 := by
  simp [polyAuto, pderiv_X]

/-- `bridge_jacobian_eq_zero` without `a₃ ≠ 0` is false: at `d = 3` and the centers `0`, `1` over `ℚ`, the Keller pair
`(x − y², y)` satisfies every other hypothesis, and its Jacobian is `1`. -/
theorem bridge_jacobian_needs_ne_zero :
    ¬ ∀ (d : ℕ) (a₃ a₄ : ℚ), a₄ ≠ 0 → a₃ ≠ a₄ → ∀ (P Q : MvPolynomial (Fin 2) ℚ),
      (∀ m ∈ P.support, m 0 + m 1 ≤ d) → (∀ m ∈ Q.support, m 0 + m 1 ≤ d) →
      BridgeConditions d a₃ a₄ (fun JL => P.coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) →
      BridgeConditions d a₃ a₄ (fun JL => Q.coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) →
      MvPolynomial.pderiv 0 P * MvPolynomial.pderiv 1 Q - MvPolynomial.pderiv 1 P * MvPolynomial.pderiv 0 Q = 0 := by
  intro h
  have hP : BridgeConditions 3 (0 : ℚ) 1
      (fun JL => (polyAuto (1 : ℚ)).coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) := by
    have : (fun JL : ℕ × ℕ => (polyAuto (1 : ℚ)).coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) =
        pAuto 1 := by
      funext JL; exact coeff_polyAuto 1 JL.1 JL.2
    rw [this]; exact bridgeConditions_zero_center 3 le_rfl 1
  have hPdeg : ∀ m ∈ (polyAuto (1 : ℚ)).support, m 0 + m 1 ≤ 3 := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, mono_eq m, coeff_polyAuto] at hm
    unfold pAuto at hm
    split_ifs at hm with h1 h2
    · simp only [Prod.mk.injEq] at h1; omega
    · simp only [Prod.mk.injEq] at h2; omega
    · exact absurd rfl hm
  have hQdeg : ∀ m ∈ (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ).support, m 0 + m 1 ≤ 3 := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, mono_eq m, coeff_y] at hm
    split_ifs at hm with h1
    · simp only [Prod.mk.injEq] at h1; omega
    · exact absurd rfl hm
  have := h 3 0 1 one_ne_zero (by norm_num) (polyAuto 1) (MvPolynomial.X 1) hPdeg hQdeg hP (bridgeConditions_y 3 0 1)
  rw [jacobian_auto] at this
  exact one_ne_zero this

end TwoDicritical
