import Mathlib

/-!
# The `E₁` valuation formula (the M3 correction, chart step)

**The order condition.** `E₁` is the blow-up of `[1:0:0]` (line at infinity `Z = 0`,
`x = X/Z`, `y = Y/Z`). In the chart `s = Y/X = y/x`, `t = Z/X = 1/x`, then
`s = s₁`, `t = s₁·t₁` with `E₁ = {s₁ = 0}` (the chart of `e1_solitary.py`,
executed in `lean/check_e1_index.py`), the affine monomial `x^i y^j` pulls back to
`s₁^{-i} · t₁^{-i-j}`. Hence the order along `E₁` is the `s₁`-exponent:

  `ν_{E₁}(x^i y^j) = -i`.

**Consequence.** `ν_{E₁} ≥ -2` means **`x`-degree at most 2** — not the paper's
"total degree at least 2" monomial condition. The paper's proof, `e1_keller_search.py`,
and `noLowTerms` of `E1Obstruction.lean` read the script's unknowns `p[J,K]` (which
index `x^{d-J-K} y^J`) as `x^J y^K`, turning the condition into total degree `≥ 2`.
At `d = 4` both monomial sets have 12 elements, which hid the mix-up; they differ.

This file formalizes the valuation formula and the 12-element coincidence purely
as exponent arithmetic (no scheme theory): the pullback is recorded as the pair of
integer exponents, and the `E₁`-order is its first component. The geometric content
(the chart substitution itself) is executed in `lean/check_e1_index.py`.
-/

namespace TwoDicritical

/-- Pullback exponents of `x^i y^j` in the `E₁` chart: `x^i y^j ↦ s₁^{-i} t₁^{-i-j}`.
    Recorded as the pair of integer exponents. -/
def e1PullbackExp (i j : ℕ) : ℤ × ℤ := (-(i : ℤ), -(i : ℤ) - (j : ℤ))

/-- **The valuation formula.** `ν_{E₁}(x^i y^j) = -i`: the `E₁`-order is minus the
    `x`-degree (the `s₁`-exponent of the pullback). -/
theorem e1_order (i j : ℕ) : (e1PullbackExp i j).1 = -(i : ℤ) := rfl

/-- The `t₁`-exponent is `-i - j` (recorded for completeness). -/
theorem e1_pullback_snd (i j : ℕ) : (e1PullbackExp i j).2 = -(i : ℤ) - (j : ℤ) := rfl

/-- **The true `E₁` condition.** `ν_{E₁} ≥ -2` holds exactly for `x`-degree at most 2.
    This is the condition `E1Open4` of `E1Keller.lean` states as `m 0 ≤ 2`. -/
theorem e1_condition_iff (i j : ℕ) : (-2 : ℤ) ≤ (e1PullbackExp i j).1 ↔ i ≤ 2 := by
  simp only [e1PullbackExp]
  omega

/-- `x³` has `E₁`-order `-3`: it satisfies the paper's "total degree ≥ 2" condition
    but not the true `E₁` condition. -/
theorem e1_x3_order : (e1PullbackExp 3 0).1 = -3 := rfl

/-- `y` has `E₁`-order `0`: it satisfies the true `E₁` condition but not the paper's
    "total degree ≥ 2" condition. -/
theorem e1_y_order : (e1PullbackExp 0 1).1 = 0 := rfl

/-- The true `E₁` set at `d = 4`: monomials of total degree `≤ 4` with `x`-degree `≤ 2`.
    It has 12 elements. -/
theorem e1_true_set_card :
    (((Finset.range 5) ×ˢ (Finset.range 5)).filter fun p : ℕ × ℕ => p.1 + p.2 ≤ 4 ∧ p.1 ≤ 2).card = 12 := by
  decide

/-- The paper's misread set at `d = 4`: monomials of total degree between 2 and 4.
    It also has 12 elements — the coincidence that hid the mix-up. -/
theorem e1_false_set_card :
    (((Finset.range 5) ×ˢ (Finset.range 5)).filter fun p : ℕ × ℕ => p.1 + p.2 ≤ 4 ∧ 2 ≤ p.1 + p.2).card = 12 := by
  decide

/-- The two 12-element sets differ: `x³` is in the misread set but has `ν = -3`. -/
theorem e1_sets_differ_x3 :
    (3, 0) ∈ ((Finset.range 5) ×ˢ (Finset.range 5)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 ≤ 4 ∧ 2 ≤ p.1 + p.2) ∧
    ¬ (-2 : ℤ) ≤ (e1PullbackExp 3 0).1 := by
  refine ⟨by decide, ?_⟩
  rw [e1_x3_order]
  norm_num

/-- The two 12-element sets differ: `y` satisfies the true condition but is excluded
    by the misread one. -/
theorem e1_sets_differ_y :
    (-2 : ℤ) ≤ (e1PullbackExp 0 1).1 ∧
    (0, 1) ∉ ((Finset.range 5) ×ˢ (Finset.range 5)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 ≤ 4 ∧ 2 ≤ p.1 + p.2) := by
  refine ⟨by decide, by decide⟩

end TwoDicritical
