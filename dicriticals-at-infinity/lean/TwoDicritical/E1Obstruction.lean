/-
  E1 degree obstruction (Theorem thm:e1 of the paper).

  Paper: "No Keller Map Admits Two Dicritical Divisors" (McCrary, Oct 2026),
  §3.2.

  Theorem (E_1 degree obstruction): Let P, Q ∈ K[X,Y] (K a field of
  characteristic 0) have every monomial x^J y^K satisfy J + K ≥ 2 (the order
  condition ν_{E_1} ≥ -2). Then [P,Q] = P_x Q_y - P_y Q_x has minimum total
  degree ≥ 2, hence cannot be a nonzero constant. In particular, (P, Q) is
  not a Keller pair.

  Proof idea: pderiv lowers the degree of each monomial by exactly 1, so
  P_x, P_y, Q_x, Q_y have no constant term (min degree ≥ 1). Products
  P_x Q_y and P_y Q_x then have min degree ≥ 2, and so does their
  difference [P,Q]. A nonzero constant has degree 0 — contradiction.

  This file is standalone (imports only Mathlib) so it compiles with
  `~/workspace/bin/lean-mathlib.sh`. Definitions are mirrored from
  Basic.lean for standalone compilation; in the project build, import
  TwoDicritical.Basic instead.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial Finsupp

variable {K : Type*} [Field K]

/-- Total degree of a monomial exponent in two variables. -/
def totDeg (s : Fin 2 →₀ ℕ) : ℕ := s 0 + s 1

/-- The Jacobian determinant `[P,Q] = P_x Q_y - P_y Q_x`. -/
noncomputable def jacobian (P Q : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q

/-- `IsKeller P Q`: the Jacobian is a nonzero constant. -/
def IsKeller (P Q : MvPolynomial (Fin 2) K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ jacobian P Q = MvPolynomial.C c

/-- Every monomial has total degree at least 2 (no constant or linear terms).
    This is the order condition `ν_{E_1} ≥ -2` from §3.2 of the paper. -/
def noLowTerms (p : MvPolynomial (Fin 2) K) : Prop :=
  ∀ s ∈ p.support, 2 ≤ totDeg s

-- ---------------------------------------------------------------------------
-- Helper: total degree is additive on monomial exponents
-- ---------------------------------------------------------------------------

lemma totDeg_add (s t : Fin 2 →₀ ℕ) : totDeg (s + t) = totDeg s + totDeg t := by
  unfold totDeg
  rw [Finsupp.add_apply, Finsupp.add_apply]
  ring

lemma single_totDeg (i : Fin 2) : totDeg (single i 1) = 1 := by
  unfold totDeg
  fin_cases i <;> simp

-- ---------------------------------------------------------------------------
-- Lemma A (paper §3.2): pderiv raises the minimum degree bound by dropping
-- each monomial's degree by exactly 1. If p has no terms of degree < 2,
-- then pderiv i p has no terms of degree < 1 (no constant term).
-- ---------------------------------------------------------------------------

lemma pderiv_minDeg {p : MvPolynomial (Fin 2) K} {i : Fin 2}
    (h : noLowTerms p) : ∀ t ∈ (pderiv i p).support, 1 ≤ totDeg t := by
  intro t ht
  rw [MvPolynomial.mem_support_iff] at ht
  rw [coeff_pderiv] at ht
  -- ht : p.coeff (t + single i 1) * (↑(t i) + 1) ≠ 0, so the first factor ≠ 0
  have hmem : t + single i 1 ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    exact ht (by rw [h0, zero_mul])
  have h2 := h _ hmem
  have hdeg : totDeg (t + single i 1) = totDeg t + 1 := by
    rw [totDeg_add, single_totDeg]
  omega

-- ---------------------------------------------------------------------------
-- Lemma B: products add minimum degrees. If f, g have no constant term,
-- then f * g has no terms of degree < 2.
-- ---------------------------------------------------------------------------

lemma mul_minDeg {f g : MvPolynomial (Fin 2) K}
    (hf : ∀ s ∈ f.support, 1 ≤ totDeg s)
    (hg : ∀ t ∈ g.support, 1 ≤ totDeg t) :
    ∀ u ∈ (f * g).support, 2 ≤ totDeg u := by
  intro u hu
  have hsub := support_mul f g hu
  rw [Finset.mem_add] at hsub
  obtain ⟨s, hs, t, ht, rfl⟩ := hsub
  have h1 := hf s hs
  have h2 := hg t ht
  rw [totDeg_add]
  omega

-- ---------------------------------------------------------------------------
-- Lemma C: differences preserve the minimum degree bound.
-- ---------------------------------------------------------------------------

lemma sub_minDeg {f g : MvPolynomial (Fin 2) K}
    (hf : ∀ s ∈ f.support, 2 ≤ totDeg s)
    (hg : ∀ t ∈ g.support, 2 ≤ totDeg t) :
    ∀ u ∈ (f - g).support, 2 ≤ totDeg u := by
  intro u hu
  have hsub : (f - g).support ⊆ f.support ∪ g.support := MvPolynomial.support_sub _ f g
  have hmem := hsub hu
  rw [Finset.mem_union] at hmem
  rcases hmem with h | h
  · exact hf u h
  · exact hg u h

-- ---------------------------------------------------------------------------
-- Theorem thm:e1 (E_1 degree obstruction): [P,Q] has minimum degree ≥ 2.
-- ---------------------------------------------------------------------------

theorem e1_degree_obstruction {P Q : MvPolynomial (Fin 2) K}
    (hP : noLowTerms P) (hQ : noLowTerms Q) :
    ∀ u ∈ (jacobian P Q).support, 2 ≤ totDeg u := by
  unfold jacobian
  apply sub_minDeg
  · apply mul_minDeg
    · exact pderiv_minDeg (i := 0) hP
    · exact pderiv_minDeg (i := 1) hQ
  · apply mul_minDeg
    · exact pderiv_minDeg (i := 1) hP
    · exact pderiv_minDeg (i := 0) hQ

-- ---------------------------------------------------------------------------
-- Corollary: (P, Q) is not a Keller pair.
-- A nonzero constant c has coeff 0 = c ≠ 0, but [P,Q] has no degree-0 term.
-- ---------------------------------------------------------------------------

theorem not_keller_of_noLowTerms {P Q : MvPolynomial (Fin 2) K}
    (hP : noLowTerms P) (hQ : noLowTerms Q) : ¬ IsKeller P Q := by
  rintro ⟨c, hc, hJ⟩
  have hc0 : (jacobian P Q).coeff 0 = c := by
    rw [hJ, coeff_C]
    simp
  have h0 : (jacobian P Q).coeff 0 = 0 := by
    have hmem : (0 : Fin 2 →₀ ℕ) ∉ (jacobian P Q).support := by
      intro hcon
      have hdeg := e1_degree_obstruction hP hQ 0 hcon
      have hzero : totDeg (0 : Fin 2 →₀ ℕ) = 0 := by
        unfold totDeg
        simp
      omega
    by_contra hne
    exact hmem (MvPolynomial.mem_support_iff.mpr hne)
  rw [h0] at hc0
  exact hc hc0.symm
