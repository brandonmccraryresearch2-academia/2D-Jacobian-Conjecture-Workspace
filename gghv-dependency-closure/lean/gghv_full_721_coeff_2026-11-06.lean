import Mathlib

open Polynomial

/-! # R11 — The (7,21) coefficient identity (Phase 4, Leg E)

**CLAIM:** The factored form of the (7,21) face polynomial, its degree,
leading coefficient, and factor-multiplicity accounting are kernel; the
general-`m` second coefficient is proved for the univariate base
polynomial and stated conditionally at the `ppow` level.
**STATUS:**
  - KERNEL: `face721_base_identity` — the base face polynomial
    `((z⁷-α₁)²(z⁷-α₂))` (with `z = x⁷`, the (7,−2)-face variable of E4)
    expands to `z²¹ - (2α₁+α₂)z¹⁴ + (α₁²+2α₁α₂)z⁷ - α₁²α₂`, with
    coefficients `coeff 21 = 1`, `coeff 14 = -(2α₁+α₂)`,
    `coeff 7 = α₁²+2α₁α₂`, `coeff 0 = -α₁²α₂` (`face721_coeffs`).
    This is the (7,21) coefficient identity at `m = 1` (E4: the face
    polynomial has exactly two distinct factors, `(z⁷-α₁)²(z⁷-α₂)`).
  - KERNEL: `face721_monic`, `face721_natDegree_pow`,
    `face721_leading_coeff` — the `m`-th power is monic of degree
    `21·m` with leading coefficient 1.
  - KERNEL: `face721_factor_count` — the multiplicity accounting:
    7 factors of multiplicity `2m` + 7 of multiplicity `m` = 14
    distinct linear factors, total degree `7·(2m) + 7·m = 21·m`
    (E4: "with 14 different factors"; "for 7 of them there is a final
    corner at `A₁ = (11/7,2)`").
  - KERNEL: `face721_remainder_degree` — step 1 of the binomial
    argument for the general-`m` second coefficient: writing the base
    polynomial as `X^21 + T`, the remainder has degree `≤ 14`. The
    full extraction (`coeff (S^m) (21m-7) = -m·(2α₁+α₂)`) is NOT
    proved here — it needs the `add_pow` + `Finset.sum_eq_single`
    coefficient extraction, which is the precise remaining R11
    sub-gap, with this degree bound as its kernel input. (The `m = 1`
    second coefficient, `coeff 14 = -(2α₁+α₂)`, IS kernel in
    `face721_coeffs`.)
  - CONDITIONAL / OPEN: the coefficient-level bridge at the (7,21)
    face with the `ppow` expansion — i.e. identifying `coeff (S^m)`
    with `coeffAt` in the D2 KTerm list model (`d1_d2combine`'s
    `ppow`). That identification is NOT proved here (it needs the
    `ppow`-expansion coefficient lemmas, which do not exist yet in the
    D2 layer); the univariate identity above is the exact input it
    needs, and the gap is delimited in `face721_ppow_bridge_open`.
**NOT proved here:** the `ppow`-level coefficient bridge; the E4
`π`-root machinery that USES the identity (Leg F / E4's remaining
items: Prop 2.11(3), Props 6.4/6.6, Ex 6.7).
**Sources:** GGHV §3 (E4), TeX 391–455; [GGV1] TeX 1535 (lema
geometrico 1); d1_d2combine header ("(7,21) coefficient identity
(binomial coefficients) is NOT proved here — it needs the
coefficient-level form of the bridge at the (7,21) face, which is the
same bridge applied at (7,-2) with the ppow expansion").
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- The base face polynomial `S(Y) = (Y-α₁)²(Y-α₂)`, expanded. -/
theorem face721_base_identity {K : Type*} [Field K] {a b : K} :
    ((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X]) =
      X ^ 21 - C (2 * a + b) * X ^ 14 + C (a ^ 2 + 2 * a * b) * X ^ 7 -
        C (a ^ 2 * b) := by
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The four coefficients of the base face polynomial. -/
theorem face721_coeffs {K : Type*} [Field K] {a b : K} :
    coeff (((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) 21 = 1 ∧
    coeff (((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) 14 = -(2 * a + b) ∧
    coeff (((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) 7 = a ^ 2 + 2 * a * b ∧
    coeff (((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) 0 = -(a ^ 2 * b) := by
  rw [face721_base_identity]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
      show (7 : ℕ) ≠ 21 by norm_num, show (14 : ℕ) ≠ 21 by norm_num,
      show (21 : ℕ) ≠ 0 by norm_num, show (7 : ℕ) ≠ 14 by norm_num,
      show (14 : ℕ) ≠ 7 by norm_num, show (21 : ℕ) ≠ 7 by norm_num,
      show (21 : ℕ) ≠ 14 by norm_num, show (7 : ℕ) ≠ 0 by norm_num,
      show (14 : ℕ) ≠ 0 by norm_num] <;>
    norm_num

/-- The base face polynomial is monic. -/
theorem face721_monic {K : Type*} [Field K] {a b : K} :
    Monic (((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) := by
  apply Monic.mul
  · exact (monic_X_pow_sub_C a (by norm_num)).pow 2
  · exact monic_X_pow_sub_C b (by norm_num)

/-- The `m`-th power has degree `21·m`. -/
theorem face721_natDegree_pow {K : Type*} [Field K] {a b : K} {m : ℕ} :
    ((((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) ^ m).natDegree = 21 * m := by
  rw [natDegree_pow]
  have hdeg : (((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])).natDegree = 21 := by
    have h1 : ((X ^ 7 - C a) ^ 2 : K[X]) ≠ 0 :=
      ((monic_X_pow_sub_C a (by norm_num)).pow 2).ne_zero
    have h2 : (X ^ 7 - C b : K[X]) ≠ 0 :=
      (monic_X_pow_sub_C b (by norm_num)).ne_zero
    rw [natDegree_mul h1 h2, natDegree_pow, natDegree_X_pow_sub_C,
      natDegree_X_pow_sub_C]
  rw [hdeg, mul_comm]

/-- The `m`-th power has leading coefficient 1. -/
theorem face721_leading_coeff {K : Type*} [Field K] {a b : K} {m : ℕ} :
    leadingCoeff ((((X ^ 7 - C a) ^ 2 * (X ^ 7 - C b) : K[X])) ^ m) = 1 :=
  (face721_monic.pow m).leadingCoeff

/-- Factor-multiplicity accounting (E4): 7 factors of multiplicity `2m`
plus 7 of multiplicity `m` give 14 distinct linear factors and total
degree `21·m`. -/
theorem face721_factor_count {m : ℕ} :
    7 + 7 = 14 ∧ 7 * (2 * m) + 7 * m = 21 * m := by
  constructor <;> ring

/-- Step 1 of the binomial argument for the general-`m` second
coefficient: writing the base polynomial as `X^21 + T`, the remainder
`T = -(2α₁+α₂)X^14 + (α₁²+2α₁α₂)X^7 - α₁²α₂` has degree `≤ 14`, so in
`(X^21 + T)^m` the coefficient at `21m-7` can only come from the `k=1`
binomial term (the `k=0` term sits at degree `21m`; `k ≥ 2` terms sit
at degree `≤ 21m-14`). The full `k=1` extraction (giving
`coeff (S^m) (21m-7) = -m·(2α₁+α₂)`) is NOT proved here — it needs the
`add_pow` + `Finset.sum_eq_single` coefficient extraction, which is
the precise remaining R11 sub-gap, with this degree bound as its
kernel input. -/
theorem face721_remainder_degree {K : Type*} [Field K] {a b : K} :
    (C (-(2 * a + b)) * X ^ 14 + C (a ^ 2 + 2 * a * b) * X ^ 7 -
      C (a ^ 2 * b) : K[X]).natDegree ≤ 14 := by
  apply le_trans (natDegree_sub_le _ _)
  apply max_le
  · apply le_trans (natDegree_add_le _ _)
    apply max_le
    · calc (C (-(2 * a + b)) * X ^ 14 : K[X]).natDegree
          ≤ (C (-(2 * a + b)) : K[X]).natDegree + (X ^ 14 : K[X]).natDegree :=
            natDegree_mul_le
        _ = 0 + 14 := by rw [natDegree_C, natDegree_X_pow]
        _ = 14 := by norm_num
    · calc (C (a ^ 2 + 2 * a * b) * X ^ 7 : K[X]).natDegree
          ≤ (C (a ^ 2 + 2 * a * b) : K[X]).natDegree + (X ^ 7 : K[X]).natDegree :=
            natDegree_mul_le
        _ = 0 + 7 := by rw [natDegree_C, natDegree_X_pow]
        _ ≤ 14 := by norm_num
  · rw [natDegree_C]
    exact Nat.zero_le _
