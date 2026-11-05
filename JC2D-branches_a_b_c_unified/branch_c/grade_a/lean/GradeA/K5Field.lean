import GradeA.IrreducibleR

open Polynomial

/-!
# K₅ = ℚ[w]/(R) is a field, with explicit extended-GCD inversion

Branch (c), A4. `R` is irreducible over `ℚ` (`Rrat_irreducible` in `GradeA.IrreducibleR`), so
`K5 := AdjoinRoot Rrat` is a field via `AdjoinRoot.instField` (Mathlib `RingTheory/AdjoinRoot.lean`).

Beyond the abstract field structure, we give the *explicit* extended-GCD inversion: for `p : ℚ[X]` with
`¬ R ∣ p`, `EuclideanDomain.gcd p R` is a unit (since `R` is irreducible), and Bézout's identity
(`EuclideanDomain.gcd_eq_gcd_ab`) exhibits `mk p` as a unit in `K5` with inverse built from
`EuclideanDomain.gcdA p R`. This is the computational content of "extended-GCD inversion over K5":
the inverse is not merely abstract (from the field axioms) but given by the Euclidean algorithm.

What is NOT done: a *verified efficient* implementation of `xgcd` on `ℚ[X]` (e.g. proving that
`EuclideanDomain.xgcd` terminates in a bounded number of steps, or extracting an efficient algorithm).
`EuclideanDomain.gcd` uses well-founded recursion, so the inverse formula below is explicit but not
kernel-computable in reasonable time. A computational `xgcd` with complexity bounds remains future work.
-/

namespace BranchC.GradeA

/-- K₅ = ℚ[w]/(R), the quintic field of branch (c). -/
abbrev K5 := AdjoinRoot Rrat

instance fact_irreducible_Rrat : Fact (Irreducible Rrat) := ⟨Rrat_irreducible⟩

/-- K₅ is a field (`AdjoinRoot.instField`, from `Rrat_irreducible`). -/
noncomputable example : Field K5 := inferInstance

open EuclideanDomain

/-- The gcd of `p` with the irreducible `R` is a unit unless `R ∣ p`.
Since `R` is irreducible, any divisor of `R` is a unit or associate to `R`;
in the latter case `R ∣ p`. -/
theorem K5_gcd_isUnit {p : ℚ[X]} (hp : ¬ Rrat ∣ p) : IsUnit (EuclideanDomain.gcd p Rrat) := by
  obtain ⟨e, he⟩ := EuclideanDomain.gcd_dvd_right p Rrat
  have hirr : Irreducible (EuclideanDomain.gcd p Rrat * e) := by
    rw [← he]; exact Rrat_irreducible
  rcases of_irreducible_mul hirr with hunit | hunit
  · exact hunit
  · exfalso
    apply hp
    obtain ⟨u, hu⟩ := hunit
    -- `Rrat = gcd * e` with `e = ↑u` a unit, so `Rrat ∣ gcd`
    have hdvd : Rrat ∣ EuclideanDomain.gcd p Rrat := ⟨(u⁻¹ : (ℚ[X])ˣ), by
      conv_rhs => rw [he]
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]⟩
    exact hdvd.trans (EuclideanDomain.gcd_dvd_left p Rrat)

/-- Explicit Bézout inversion: `(mk p) * (mk (gcdA p R)) = mk (gcd p R)` in `K5`.
The `R * (gcdB p R)` term vanishes in the quotient. -/
theorem K5_bezout {p : ℚ[X]} :
    (AdjoinRoot.mk Rrat p) * (AdjoinRoot.mk Rrat (gcdA p Rrat))
      = AdjoinRoot.mk Rrat (EuclideanDomain.gcd p Rrat) := by
  have hbez := gcd_eq_gcd_ab p Rrat
  have h : p * gcdA p Rrat = EuclideanDomain.gcd p Rrat - Rrat * gcdB p Rrat := by
    rw [hbez]; ring
  calc (AdjoinRoot.mk Rrat p) * (AdjoinRoot.mk Rrat (gcdA p Rrat))
      = AdjoinRoot.mk Rrat (p * gcdA p Rrat) := by rw [map_mul]
    _ = AdjoinRoot.mk Rrat (EuclideanDomain.gcd p Rrat - Rrat * gcdB p Rrat) := by rw [h]
    _ = AdjoinRoot.mk Rrat (EuclideanDomain.gcd p Rrat) := by
        rw [map_sub]
        have hz : AdjoinRoot.mk Rrat (Rrat * gcdB p Rrat) = 0 := by
          rw [map_mul, AdjoinRoot.mk_self, zero_mul]
        rw [hz, sub_zero]

/-- Every `p` not divisible by `R` gives a unit in `K5`, via the explicit Bézout inverse.
This is the extended-GCD inversion: `mk p` is invertible, with inverse built from `gcdA`. -/
theorem K5_isUnit_mk {p : ℚ[X]} (hp : ¬ Rrat ∣ p) : IsUnit (AdjoinRoot.mk Rrat p) := by
  have h1 : IsUnit (AdjoinRoot.mk Rrat (EuclideanDomain.gcd p Rrat)) := (K5_gcd_isUnit hp).map _
  rw [← K5_bezout] at h1
  exact isUnit_of_mul_isUnit_left h1

end BranchC.GradeA
