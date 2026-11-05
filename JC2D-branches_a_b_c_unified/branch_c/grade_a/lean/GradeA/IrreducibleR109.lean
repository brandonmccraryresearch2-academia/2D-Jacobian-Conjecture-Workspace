import GradeA.R109Data
import GradeA.IrreducibleR

/-!
# `R = X⁵ − X⁴ + 3X³ + 3X² + 26` is irreducible modulo 109, with determinant transfer

Branch (c), A3. Irreducibility is certified by the two Bézout identities in `R109Data.lean`
(the "two gcds" against `X^(109^i) - X`):

* `bezout_lin`: `u1 * R + v1 * (X^109 - X) = 1`, so `R` has no root in `𝔽₁₀₉`.
* `quad_coprime`: `IsCoprime R (X^(109²) - X)` (from `bezout_quad_small` + `quad_mod`), so `R` has no
  monic divisor of degree 1 or 2: any such divisor shares a nontrivial common factor with
  `X^(109²) - X` (a monic linear always divides it; a monic irreducible quadratic divides it by
  `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`).

Since `R` is monic of degree 5 (prime), this gives `Irreducible R109`
(`Polynomial.Monic.irreducible_iff_lt_natDegree_lt`).

Finally, reduction mod 109 gives a ring hom `quotReduce109 : ℤ[X]/(R) →+* 𝔽₁₀₉[X]/(R̄)`, and determinant
commutes with it (`RingHom.map_det`, Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean`), so a nonzero
minor mod 109 lifts (`det_transfer_109`). Since `R̄` is irreducible, the target is a field.

No `sorry`.
-/

open Polynomial

namespace BranchC.GradeA

lemma R109_natDegree : R109.natDegree = 5 := by
  unfold R109; compute_degree!

lemma R109_monic : R109.Monic := by
  unfold R109; monicity!

lemma R109_ne_one : R109 ≠ 1 := by
  intro h
  have h5 := R109_natDegree
  rw [h, natDegree_one] at h5
  exact absurd h5 (by norm_num)

/-! ### No root: from the linear Bézout -/

/-- `R` has no root in `𝔽₁₀₉`. From `bezout_lin`: evaluating `u1*R + v1*(X^109-X) = 1` at a root `r`
gives `(v1.eval r) * (r^109 - r) = 1`, but `r^109 = r` (`FiniteField.pow_card`), so `0 = 1`. -/
theorem R109_no_root (r : ZMod 109) : ¬ R109.IsRoot r := by
  intro h
  have heval : (u1 * R109 + v1 * (X ^ 109 - X)).eval r = 1 := by
    rw [bezout_lin, eval_one]
  rw [eval_add, eval_mul, eval_mul, h, mul_zero, zero_add, eval_sub, eval_pow, eval_X] at heval
  -- heval : (v1.eval r) * (r ^ 109 - r) = 1
  have hfermat : r ^ 109 = r := FiniteField.pow_card r
  rw [hfermat, sub_self, mul_zero] at heval
  exact zero_ne_one heval

/-! ### Coprimality with `X^(109²) - X` -/

set_option maxRecDepth 10000 in
/-- `IsCoprime R (X^(109²) - X)`, from the small Bézout and the modular reduction.
Write `X^(109²) - X = Q * R + S` (with `Q` the quotient, `S = S109` by `quad_mod`); then
`(aq - bq*Q) * R + bq * (X^(109²) - X) = 1`. -/
theorem quad_coprime : IsCoprime R109 (X ^ (109 ^ 2) - X) := by
  obtain ⟨a, b, hab⟩ := (⟨aq, bq, bezout_quad_small⟩ : IsCoprime R109 S109)
  have hdiv : X ^ (109 ^ 2) - X = ((X ^ (109 ^ 2) - X) / R109) * R109 + S109 := by
    have h := EuclideanDomain.div_add_mod' (X ^ (109 ^ 2) - X) R109
    rw [quad_mod] at h
    exact h.symm
  refine ⟨a - b * ((X ^ (109 ^ 2) - X) / R109), b, ?_⟩
  linear_combination hab + b * hdiv

/-! ### Every monic irreducible quadratic divisor shares a factor with `X^(109²) - X` -/

/-- A monic irreducible quadratic divides `X^(109²) - X`
(`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`). -/
lemma irred_quad_dvd_X_pow (q : (ZMod 109)[X]) (hi : Irreducible q) (hd : q.natDegree = 2) :
    q ∣ X ^ (109 ^ 2) - X := by
  have h := (hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 2)).mp (by rw [hd])
  rwa [show Nat.card (ZMod 109) = 109 from by simp] at h

/-- A reducible monic quadratic has a monic linear divisor. -/
lemma monic_linear_dvd_of_reducible (q : (ZMod 109)[X]) (hq : q.Monic) (hd : q.natDegree = 2)
    (hi : ¬ Irreducible q) : ∃ d, d.Monic ∧ d.natDegree = 1 ∧ d ∣ q := by
  have hq_ne : q ≠ 0 := hq.ne_zero
  have hq_not_unit : ¬ IsUnit q := by
    intro h
    rw [Polynomial.isUnit_iff_degree_eq_zero] at h
    have h2 : q.degree = 2 := by
      rw [Polynomial.degree_eq_natDegree hq_ne, hd]
      norm_num
    rw [h] at h2
    exact absurd h2 (by decide)
  have hi' : IsUnit q ∨ ∃ f g, q = f * g ∧ ¬IsUnit f ∧ ¬IsUnit g := by
    by_cases hu : IsUnit q
    · exact Or.inl hu
    · right
      have h2 : ¬ ∀ a b, q = a * b → IsUnit a ∨ IsUnit b := fun h => hi ⟨hu, h⟩
      push Not at h2
      exact h2
  rcases hi' with h | ⟨f, g, hfg, hf, hg⟩
  · exact absurd h hq_not_unit
  · -- q = f * g, f g non-units, nonzero; so natDegree f = natDegree g = 1
    have hf_ne : f ≠ 0 := fun h0 => hq_ne (by rw [hfg, h0, zero_mul])
    have hg_ne : g ≠ 0 := fun h0 => hq_ne (by rw [hfg, h0, mul_zero])
    have hdeg : f.natDegree + g.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul hf_ne hg_ne, ← hfg, hd]
    have hf_pos : 1 ≤ f.natDegree := by
      rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
      · exfalso
        apply hf
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hf_ne, h0]
        rfl
      · exact hpos
    have hg_pos : 1 ≤ g.natDegree := by
      rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
      · exfalso
        apply hg
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hg_ne, h0]
        rfl
      · exact hpos
    have hf1 : f.natDegree = 1 := by omega
    -- d = C (f.coeff 1)⁻¹ * f is monic linear dividing q
    have hfc : f.coeff 1 ≠ 0 := by
      have h : f.coeff f.natDegree = f.leadingCoeff := Polynomial.coeff_natDegree
      rw [hf1] at h
      rw [h]
      exact Polynomial.leadingCoeff_ne_zero.mpr hf_ne
    have hC_ne : C ((f.coeff 1)⁻¹) ≠ 0 := by
      rw [ne_eq, Polynomial.C_eq_zero]
      exact inv_ne_zero hfc
    have hnat : (C ((f.coeff 1)⁻¹) * f).natDegree = 1 := by
      rw [Polynomial.natDegree_mul hC_ne hf_ne, Polynomial.natDegree_C, hf1]
    refine ⟨C ((f.coeff 1)⁻¹) * f, ?_, hnat, ?_⟩
    · -- monic: leading coeff is 1
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, Polynomial.coeff_C_mul]
      exact inv_mul_cancel₀ hfc
    · -- divides q: d ∣ f ∣ q
      have hdf : C ((f.coeff 1)⁻¹) * f ∣ f := by
        use C (f.coeff 1)
        rw [mul_assoc, mul_comm f (C (f.coeff 1)), ← mul_assoc,
          ← Polynomial.C_mul, inv_mul_cancel₀ hfc, map_one, one_mul]
      rw [hfg]
      exact dvd_mul_of_dvd_left hdf g

/-- A degree-1 polynomial over `𝔽₁₀₉` has a root. -/
lemma exists_root_of_natDegree_eq_one {p : (ZMod 109)[X]} (hp : p.natDegree = 1) :
    ∃ r, p.IsRoot r := by
  have hp_ne : p ≠ 0 := by
    rintro rfl
    simp at hp
  have h1 : p.coeff 1 ≠ 0 := by
    have h : p.coeff p.natDegree = p.leadingCoeff := Polynomial.coeff_natDegree
    rw [hp] at h
    rw [h]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp_ne
  have hp_eq : p = C (p.coeff 1) * X + C (p.coeff 0) := by
    have h2 : p.natDegree < 2 := by omega
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' p h2]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp [pow_zero, pow_one, add_comm]
  use -(p.coeff 0) / (p.coeff 1)
  nth_rewrite 1 [hp_eq]
  simp only [Polynomial.IsRoot, eval_add, eval_mul, eval_C, eval_X]
  field_simp
  ring

/-- If `q ∣ R` and `q` has a root, so does `R`. -/
lemma isRoot_of_dvd {q R : (ZMod 109)[X]} {r : ZMod 109} (hdiv : q ∣ R) (hroot : q.IsRoot r) :
    R.IsRoot r := by
  obtain ⟨s, hs⟩ := hdiv
  show R.eval r = 0
  rw [hs, eval_mul, hroot, zero_mul]

set_option maxRecDepth 100000 in
/-- No monic divisor of degree 1 or 2. -/
theorem R109_no_small_dvd (q : (ZMod 109)[X]) (hq : q.Monic)
    (hdeg : q.natDegree = 1 ∨ q.natDegree = 2) : ¬ q ∣ R109 := by
  intro hdiv
  rcases hdeg with h1 | h2
  · -- degree 1: has a root, so R109 has a root
    obtain ⟨r, hr⟩ := exists_root_of_natDegree_eq_one h1
    exact R109_no_root r (isRoot_of_dvd hdiv hr)
  · by_cases hi : Irreducible q
    · -- irreducible quadratic: divides X^(109^2)-X, contradicts coprimality
      have hdvd : q ∣ X ^ (109 ^ 2) - X := irred_quad_dvd_X_pow q hi h2
      obtain ⟨U, V, hUV⟩ := quad_coprime
      have h1 : q ∣ (1 : (ZMod 109)[X]) := by
        have : q ∣ U * R109 + V * (X ^ (109 ^ 2) - X) := dvd_add
          (dvd_mul_of_dvd_right hdiv U) (dvd_mul_of_dvd_right hdvd V)
        rwa [hUV] at this
      have hunit : IsUnit q := isUnit_of_dvd_one h1
      rw [Polynomial.isUnit_iff_degree_eq_zero] at hunit
      have hdeg2 : q.degree = 2 := by
        rw [Polynomial.degree_eq_natDegree hq.ne_zero, h2]; norm_num
      rw [hunit] at hdeg2
      exact absurd hdeg2 (by decide)
    · -- reducible: has a monic linear divisor, which has a root
      obtain ⟨d, hd_monic, hd_deg, hd_dvd⟩ := monic_linear_dvd_of_reducible q hq h2 hi
      have hd_R : d ∣ R109 := hd_dvd.trans hdiv
      obtain ⟨r, hr⟩ := exists_root_of_natDegree_eq_one hd_deg
      exact R109_no_root r (isRoot_of_dvd hd_R hr)

/-! ### Irreducibility -/

/-- **`R` is irreducible modulo 109.** -/
theorem R109_irreducible : Irreducible R109 := by
  rw [R109_monic.irreducible_iff_lt_natDegree_lt R109_ne_one]
  intro q hq hdeg hdvd
  rw [R109_natDegree, Finset.mem_Ioc] at hdeg
  have h12 : q.natDegree = 1 ∨ q.natDegree = 2 := by
    have : (5 : ℕ) / 2 = 2 := by norm_num
    omega
  exact R109_no_small_dvd q hq h12 hdvd

/-! ### Determinant transfer through reduction mod 109 -/

/-- Reduction of coefficients mod 109. -/
noncomputable def reduceMod109 : ℤ[X] →+* (ZMod 109)[X] :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod 109))

/-- `R` maps to `R109` under reduction. -/
lemma reduceMod109_R : Rint.map (Int.castRingHom (ZMod 109)) = R109 := by
  simp [Rint, R109]

/-- The reduction map induces `ℤ[X]/(R) →+* 𝔽₁₀₉[X]/(R̄)`. Well-defined because `R ↦ R̄ = 0`. -/
noncomputable def quotReduce109 :
    (ℤ[X] ⧸ Ideal.span {Rint}) →+* ((ZMod 109)[X] ⧸ Ideal.span {R109}) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp reduceMod109) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨g, rfl⟩ := ha
    show ((Ideal.Quotient.mk _).comp reduceMod109) (Rint * g) = 0
    rw [RingHom.comp_apply, map_mul]
    have hR : reduceMod109 Rint = R109 := by
      unfold reduceMod109; rw [Polynomial.coe_mapRingHom]; exact reduceMod109_R
    rw [hR, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨reduceMod109 g, rfl⟩)

/-- **Determinant transfer mod 109.** Determinant commutes with the reduction hom (`RingHom.map_det`,
Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean`), so a nonzero minor mod 109 lifts to a nonzero minor
over `ℤ[X]/(R)`. Since `R̄` is irreducible (`R109_irreducible`), the target is a field. -/
theorem det_transfer_109 {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (ℤ[X] ⧸ Ideal.span {Rint}))
    (hdet : (quotReduce109.mapMatrix M).det ≠ 0) : M.det ≠ 0 := by
  have h1 : quotReduce109 M.det = (quotReduce109.mapMatrix M).det :=
    RingHom.map_det quotReduce109 M
  rw [← h1] at hdet
  exact fun hx => hdet (by rw [hx, map_zero])

end BranchC.GradeA
