import TwoDicritical.BridgeCollapse

/-!
# One center already forces degree at most 2

The bridge equations at a single nonzero center `a` (weights `W ≥ 2`, `i ≤ W − 2`) kill every coefficient of weight
`2J + L ≥ 3` and leave one relation at weight 2, `p(0,2) = −a·p(1,0)` (`bridge_one_center`). So the solutions are
`span{1, y, x − a·y²}`: polynomials of degree at most 2. In geometric terms (`lean/README.md`): over a free point `a`
of `E₂` the condition `ord_b S_a ≥ 2d − 1` says `ν ≥ −1` on the divisor over `a`, and the valuation there is minus the
degree in the coordinates `(x − a·y², y)`.

Consequences recorded here:
* `bridge_one_center`: with one nonzero center, the weight-≥3 coefficients vanish and `p(0,2) = −a·p(1,0)`;
* `zero_center_no_top_degree`: under `BridgeConditions d 0 a₄` with `a₄ ≠ 0` and `d ≥ 3`, every coefficient of total
  degree `d` vanishes. The witness `x − a₄·y²` of `CenterHypotheses.lean` has degree 2, below `d`: it exists only
  because `d` is a bound on the degree, not the degree.

The weight-≥3 step is `block_vanish` of `BridgeCollapse.lean` at one center; the second center of `bridge_collapse`
is used only at weight 2.
-/

open Finset

namespace TwoDicritical

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The weight-2 bridge equation, written out: `p(0,2)·a^(d−2) + p(1,0)·a^(d−1)`. -/
theorem bridgeEq_two (d : ℕ) (hd : 2 ≤ d) (a : K) (p : ℕ × ℕ → K) :
    bridgeEq d 2 0 a p = p (0, 2) * a ^ (d - 2) + p (1, 0) * a ^ (d - 1) := by
  unfold bridgeEq
  have hIco : Ico (2 - d) (2 / 2 + 1) = {0, 1} := by
    have : 2 - d = 0 := by omega
    rw [this]; decide
  rw [hIco, Finset.sum_pair (by norm_num)]
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
  congr 2

/-- **One center.** If every bridge equation at the single nonzero center `a` holds, then every coefficient of weight
`2J + L ≥ 3` vanishes, and (for `d ≥ 2`) `p(0,2) = −a·p(1,0)`. -/
theorem bridge_one_center (d : ℕ) (a : K) (ha : a ≠ 0) (p : ℕ × ℕ → K)
    (h : ∀ W i, 2 ≤ W → i + 2 ≤ W → bridgeEq d W i a p = 0) :
    (∀ J L : ℕ, J + L ≤ d → 3 ≤ 2 * J + L → p (J, L) = 0) ∧ (2 ≤ d → p (0, 2) = -(a * p (1, 0))) := by
  constructor
  · intro J L hJL hW
    set W := 2 * J + L with hWdef
    have hmem : J ∈ Ico (W - d) (W / 2 + 1) := by rw [Finset.mem_Ico]; omega
    have hL : L = W - 2 * J := by omega
    rw [hL]
    exact block_vanish d W a ha p (by omega) (fun i hi => h W i (by omega) hi) J hmem
  · intro hd
    have e := h 2 0 le_rfl le_rfl
    rw [bridgeEq_two d hd] at e
    have hd1 : a ^ (d - 1) = a ^ (d - 2) * a := by rw [← pow_succ]; congr 1; omega
    rw [hd1] at e
    have : a ^ (d - 2) * (p (0, 2) + a * p (1, 0)) = 0 := by linear_combination e
    have h2 := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ ha)
    linear_combination h2

/-- **A center at `0` and the exact degree.** Under the bridge conditions at `0` and at `a₄ ≠ 0`, with `d ≥ 3`, every
coefficient of total degree `d` vanishes: no polynomial of exact degree `d ≥ 3` satisfies them. -/
theorem zero_center_no_top_degree (d : ℕ) (hd : 3 ≤ d) (a₄ : K) (h₄ : a₄ ≠ 0) (p : ℕ × ℕ → K)
    (hp : BridgeConditions d 0 a₄ p) : ∀ J L : ℕ, J + L = d → p (J, L) = 0 := by
  intro J L hJL
  exact (bridge_one_center d a₄ h₄ p (fun W i hW hi => (hp W i hW hi).2)).1 J L (by omega) (by omega)

end TwoDicritical
