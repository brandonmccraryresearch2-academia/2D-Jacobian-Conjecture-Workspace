import Mathlib
import TwoDicritical.BlockRank

/-!
# The `m = 1` bridge collapse (Theorem `thm:bridge` of "No Keller Map Admits Two Dicritical Divisors"), without axioms

The draft `Bridge.lean` of 2026-10-12 derived this theorem from two axioms, `bridge_triangular` and
`block_full_rank`. Both are false as stated (review of 2026-10-12, `reviews/lean/BridgeAxiomsInconsistent.lean`):
Lean quantifies them over every system, not over the paper's. This file proves the theorem from the paper's
explicit equations instead, and uses `choose_det_ne_zero` of `BlockRank.lean` (unchanged) for the rank step.

**The equations.** For `S = Σ p_{JK} x^J y^K` with `J + K ≤ d`, the paper's pullback at a center `a` is
`S_a(b) = Σ p_{JK} (a + ã b)^(d-J-K) b^(2d-2J-K)`, and the bridge condition is `ord_b S_a ≥ 2d - 1` at both centers.
Expanding `(a + ã b)^e = Σ_i C(e,i) a^(e-i) ã^i b^i`, the coefficient of `ã^i b^t` collects exactly the monomials of
weight `W = 2J + K = 2d - t + i`. Reading `ã` as an indeterminate, as the paper's equation (eq:block) does, each
coefficient vanishes separately, and the conditions are

  `bridgeEq d W i a p = Σ_{W-d ≤ J ≤ W/2} p(J, W-2J) · C(d+J-W, i) · a^(d+J-W-i) = 0`  for `0 ≤ i ≤ W - 2`.

(`t ≤ 2d - 2` gives `i ≤ W - 2`.) So the system is **block-diagonal** in `W`: no triangularity is needed.

**The proof** (`bridge_collapse`): fix `W ≥ 2`; the weight-`W` variables are `n = ⌊W/2⌋ + 1 - max(0, W-d)` values of
`J`, with exponents `e = d + J - W`, which are distinct.
* If `n ≤ W - 1`, the equations `i = 0, …, n-1` at one center, multiplied by `a^i`, read `Σ_k C(e_k, i) q_k = 0`
  with `q_k = p_k a^(e_k)`; `det [C(e_k, i)] ≠ 0` (`choose_det_ne_zero`), so `q = 0` and `p = 0`.
* Otherwise `W = 2` and `n = 2` (`d ≥ 2`): the variables are `p(1,0)` and `p(0,2)`, there is one equation (`i = 0`)
  per center, and `a^(d-2)(p(1,0)·a + p(0,2)) = 0` at the two distinct nonzero centers forces both to vanish. **The
  paper's proof cites the block-rank lemma here, whose hypothesis `m ≥ n` fails (`m = W - 1 = 1 < 2 = n`); the two
  centers are needed.**

Every `p(J,K)` with `2J + K ≥ 2` vanishes: only `1` and `y` survive (`bridge_collapse`), so `[P,Q] = 0` for any two
polynomials in the bridge (`bridge_jacobian_eq_zero`).

What this file does not formalize: the derivation of the equations from the resolution geometry (the pullback formula
(eq:bridge-pullback), and the reading of `ã` as an indeterminate). Those are premises, stated here as the definition
`bridgeEq`.
-/

open Finset Matrix

namespace TwoDicritical

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient of `ã^i b^(2d-W+i)` of the pullback at the center `a`: the weight-`W` variables are `(J, W - 2J)`
with `W - d ≤ J ≤ W/2`, and `e = d + J - W`. -/
noncomputable def bridgeEq (d W i : ℕ) (a : K) (p : ℕ × ℕ → K) : K :=
  ∑ J ∈ Ico (W - d) (W / 2 + 1), p (J, W - 2 * J) * (Nat.choose (d + J - W) i : K) * a ^ (d + J - W - i)

/-- The bridge conditions at both centers: all coefficients `ã^i b^t`, `t ≤ 2d - 2`, vanish. -/
def BridgeConditions (d : ℕ) (a₃ a₄ : K) (p : ℕ × ℕ → K) : Prop :=
  ∀ W i, 2 ≤ W → i + 2 ≤ W → bridgeEq d W i a₃ p = 0 ∧ bridgeEq d W i a₄ p = 0

/-- One center, when the block has at most `W - 1` columns. -/
theorem block_vanish (d W : ℕ) (a : K) (ha : a ≠ 0) (p : ℕ × ℕ → K)
    (hn : W / 2 + 1 - (W - d) ≤ W - 1) (h : ∀ i, i + 2 ≤ W → bridgeEq d W i a p = 0) :
    ∀ J ∈ Ico (W - d) (W / 2 + 1), p (J, W - 2 * J) = 0 := by
  set J₀ := W - d with hJ₀
  set n := W / 2 + 1 - J₀ with hn_def
  -- exponents along the block
  let e : Fin n → ℕ := fun k => d + (J₀ + k) - W
  have hJW : ∀ k : Fin n, W ≤ d + (J₀ + k) := by intro k; omega
  have he : Function.Injective e := by
    intro k k' hkk
    simp only [e] at hkk
    have := hJW k; have := hJW k'
    exact Fin.ext (by omega)
  let q : Fin n → K := fun k => p (J₀ + k, W - 2 * (J₀ + k)) * a ^ (e k)
  -- the n × n system
  have hsys : (Matrix.of fun i k : Fin n => (Nat.choose (e k) i.val : K)) *ᵥ q = 0 := by
    funext i
    have hi : i.val + 2 ≤ W := by have := i.isLt; omega
    have h0 := h i.val hi
    unfold bridgeEq at h0
    rw [Finset.sum_Ico_eq_sum_range, ← hn_def, ← Fin.sum_univ_eq_sum_range] at h0
    have h1 : a ^ i.val * (∑ k : Fin n, p (J₀ + k, W - 2 * (J₀ + k)) * (Nat.choose (d + (J₀ + k) - W) i.val : K)
        * a ^ (d + (J₀ + k) - W - i.val)) = 0 := by rw [h0, mul_zero]
    rw [Finset.mul_sum] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, q, e]
    rw [← h1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hik : i.val ≤ d + (J₀ + k) - W
    · have hpow : a ^ i.val * a ^ (d + (J₀ + k) - W - i.val) = a ^ (d + (J₀ + k) - W) := by
        rw [← pow_add]; congr 1; omega
      rw [← hpow]; ring
    · have hc : Nat.choose (d + (J₀ + k) - W) i.val = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hc]
  have hq : q = 0 := Matrix.eq_zero_of_mulVec_eq_zero (choose_det_ne_zero he) hsys
  intro J hJ
  rw [Finset.mem_Ico] at hJ
  have hk : J - J₀ < n := by omega
  have hqk := congrFun hq ⟨J - J₀, hk⟩
  simp only [q, Pi.zero_apply] at hqk
  have hJeq : J₀ + (J - J₀) = J := by omega
  rw [hJeq] at hqk
  exact (mul_eq_zero.mp hqk).resolve_right (pow_ne_zero _ ha)

omit [CharZero K] in
/-- The weight-2 block (`d ≥ 2`): two variables, one equation per center. -/
theorem block_vanish_two (d : ℕ) (hd : 2 ≤ d) (a₃ a₄ : K) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0) (hne : a₃ ≠ a₄)
    (p : ℕ × ℕ → K) (e₃ : bridgeEq d 2 0 a₃ p = 0) (e₄ : bridgeEq d 2 0 a₄ p = 0) :
    p (1, 0) = 0 ∧ p (0, 2) = 0 := by
  have hsum : ∀ a : K, bridgeEq d 2 0 a p = p (0, 2) * a ^ (d - 2) + p (1, 0) * a ^ (d - 1) := by
    intro a
    unfold bridgeEq
    have hIco : Ico (2 - d) (2 / 2 + 1) = {0, 1} := by
      have : 2 - d = 0 := by omega
      rw [this]; decide
    rw [hIco, Finset.sum_pair (by norm_num)]
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    congr 2
  rw [hsum] at e₃ e₄
  -- a^(d-2) (p(0,2) + p(1,0) a) = 0
  have hfac : ∀ a : K, a ≠ 0 → p (0, 2) * a ^ (d - 2) + p (1, 0) * a ^ (d - 1) = 0 →
      p (0, 2) + p (1, 0) * a = 0 := by
    intro a ha he
    have hd1 : a ^ (d - 1) = a ^ (d - 2) * a := by rw [← pow_succ]; congr 1; omega
    rw [hd1] at he
    have : a ^ (d - 2) * (p (0, 2) + p (1, 0) * a) = 0 := by linear_combination he
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ ha)
  have l₃ := hfac a₃ h₃ e₃
  have l₄ := hfac a₄ h₄ e₄
  have h10 : p (1, 0) = 0 := by
    have : p (1, 0) * (a₃ - a₄) = 0 := by linear_combination l₃ - l₄
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  refine ⟨h10, ?_⟩
  rw [h10, zero_mul, add_zero] at l₃
  exact l₃

/-- **Bridge collapse (Theorem `thm:bridge`).** Under the bridge conditions at two distinct nonzero centers, every
coefficient `p(J,K)` with `J + K ≤ d` and `2J + K ≥ 2` vanishes: the solutions are `span{1, y}`. -/
theorem bridge_collapse (d : ℕ) (a₃ a₄ : K) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0) (hne : a₃ ≠ a₄)
    (p : ℕ × ℕ → K) (hp : BridgeConditions d a₃ a₄ p) :
    ∀ J L : ℕ, J + L ≤ d → 2 ≤ 2 * J + L → p (J, L) = 0 := by
  intro J L hJL hW
  set W := 2 * J + L with hWdef
  have hmem : J ∈ Ico (W - d) (W / 2 + 1) := by rw [Finset.mem_Ico]; omega
  have hL : L = W - 2 * J := by omega
  rw [hL]
  by_cases hn : W / 2 + 1 - (W - d) ≤ W - 1
  · exact block_vanish d W a₃ h₃ p hn (fun i hi => (hp W i hW hi).1) J hmem
  · -- then W = 2 and d ≥ 2
    have hW2 : W = 2 := by omega
    have hd : 2 ≤ d := by omega
    obtain ⟨h10, h02⟩ := block_vanish_two d hd a₃ a₄ h₃ h₄ hne p
      (by have := (hp 2 0 le_rfl le_rfl).1; exact this) (by have := (hp 2 0 le_rfl le_rfl).2; exact this)
    have hJ : J = 0 ∨ J = 1 := by omega
    rcases hJ with rfl | rfl
    · simpa [hW2] using h02
    · simpa [hW2] using h10

/-- **No Keller pair in the bridge.** If the coefficients of `P` and `Q` (as functions `ℕ × ℕ → K`, supported on
`J + K ≤ d`) both satisfy the bridge conditions, then `P` and `Q` are polynomials in `y` alone of degree ≤ 1, and
their Jacobian vanishes. Stated for `MvPolynomial (Fin 2) K` with `x = X 0`, `y = X 1`. -/
theorem bridge_jacobian_eq_zero (d : ℕ) (a₃ a₄ : K) (h₃ : a₃ ≠ 0) (h₄ : a₄ ≠ 0) (hne : a₃ ≠ a₄)
    (P Q : MvPolynomial (Fin 2) K)
    (hPdeg : ∀ m ∈ P.support, m 0 + m 1 ≤ d) (hQdeg : ∀ m ∈ Q.support, m 0 + m 1 ≤ d)
    (hP : BridgeConditions d a₃ a₄ (fun JL => P.coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)))
    (hQ : BridgeConditions d a₃ a₄ (fun JL => Q.coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2))) :
    MvPolynomial.pderiv 0 P * MvPolynomial.pderiv 1 Q - MvPolynomial.pderiv 1 P * MvPolynomial.pderiv 0 Q = 0 := by
  -- every monomial of P and Q is 1 or y
  have hsupp : ∀ (F : MvPolynomial (Fin 2) K), (∀ m ∈ F.support, m 0 + m 1 ≤ d) →
      BridgeConditions d a₃ a₄ (fun JL => F.coeff (Finsupp.single 0 JL.1 + Finsupp.single 1 JL.2)) →
      ∀ m ∈ F.support, m 0 = 0 ∧ m 1 ≤ 1 := by
    intro F hF hFb m hm
    have hm' : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
      ext i; fin_cases i <;> simp
    by_contra hcon
    have h2 : 2 ≤ 2 * m 0 + m 1 := by omega
    have := bridge_collapse d a₃ a₄ h₃ h₄ hne _ hFb (m 0) (m 1) (hF m hm) h2
    simp only at this
    rw [← hm'] at this
    exact (MvPolynomial.mem_support_iff.mp hm) this
  -- such polynomials have zero x-derivative
  have hdx : ∀ (F : MvPolynomial (Fin 2) K), (∀ m ∈ F.support, m 0 = 0 ∧ m 1 ≤ 1) →
      MvPolynomial.pderiv 0 F = 0 := by
    intro F hF
    rw [MvPolynomial.as_sum F, map_sum]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    rw [MvPolynomial.pderiv_monomial, (hF m hm).1]
    simp
  rw [hdx P (hsupp P hPdeg hP), hdx Q (hsupp Q hQdeg hQ), zero_mul, mul_zero, sub_zero]

end TwoDicritical
