import Mathlib

open MvPolynomial

/-! # R14 — D2 polynomial versions: bilinearity / chain rule / Jacobi
(Phase 4, Leg E)

**CLAIM:** The Poisson bracket on `MvPolynomial (Fin 2) ℚ` is bilinear,
antisymmetric, and Leibniz; Jacobi is attempted; the translation chain
rule is conditional on the exact commutation lemma.
**STATUS:**
  - KERNEL: `pbracket_antisymm`, `pbracket_add_left`,
    `pbracket_add_right`, `pbracket_smul`, `pbracket_leibniz` — the
    polynomial versions of the bracket laws whose monomial versions
    are kernel in Phase 1 (`d1_extremos` / `d1_central`: `brkTerm_*`,
    `bracket_*`, `leibniz_coeff`). The bracket here is the honest
    Poisson bracket `[f,g] = f_x·g_y - f_y·g_x` on two-variable
    polynomials over `ℚ`.
  - KERNEL: `pbracket_jacobi` — the Jacobi identity, via the
    in-file `pderiv_comm` (partial derivatives commute, proved here by
    `MvPolynomial.induction_on'` on monomials; there is NO
    `MvPolynomial.pderiv_pderiv_comm` in this Mathlib — the probe
    confirmed it does not exist) and the terminating one-direction
    form `pderiv_comm01` used as the simp normalizer. VM-verified
    2026-11-06 (FULL exit 0; axioms [propext, Classical.choice,
    Quot.sound]) and second-tool-checked in Singular 4.3.1
    (`JACOBI = 0` on concrete polynomials).
  - CONDITIONAL: `pbracket_translate` — the chain rule for the
    translation `φ(y) = y + μ` (the polynomial model of the
    φ-preserva-el-Jacobiano principle used in esquina(3)'s φ-argument
    and in GGHV §4's `φ₂`): `[φ(f), φ(g)] = φ([f,g)]`, from the
    explicit commutation premise `hchain : pderiv i (φ f) = φ (pderiv i
    f)`. That commutation is the exact missing lemma (no
    `MvPolynomial.pderiv_aeval` was available when this file was
    written); proving it would close the chain rule unconditionally.
  - KERNEL: `joseph_counterexample_bracket` — the bracket value in the
    Joseph 2.2 counterexample (R9): for `A = y(x²+1)+x`, `B = x`,
    `[A,B] = -(x²+1)`, so `AB/[A,B] = -xy - x²/(x²+1)` as a rational
    function. (The non-membership `x²/(x²+1) ∉ K[x,y]` is a degree
    argument, recorded in R9's header, not proved here.)
**NOT proved here:** Jacobi (if the attempt fails — see above); the
`pderiv`/`aeval` commutation; the Laurent chain rule for
`φ(y) = y + μx⁻³` (needs the Laurent bracket, not the polynomial one).
**Sources:** [GGV1] TeX 480 (commutator-valuation, which needs the
bracket laws at polynomial level); inventory.md §A "Laurent algebra
(D2)" row (monomial bracket/φ chain rule + monomial Jacobi KERNEL;
polynomial versions OPEN).
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- Partial derivatives commute (there is no
`MvPolynomial.pderiv_pderiv_comm` in this Mathlib — probe-confirmed).
Proved by induction on the polynomial (`induction_on'`: monomial +
add cases); the monomial case reduces to a Finsupp exponent identity
(closed by `omega` after case-splitting on the indices) plus the
coefficient identity `a * s j * s i = a * s i * s j`. -/
theorem pderiv_comm (i j : Fin 2) (f : MvPolynomial (Fin 2) ℚ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  induction f using MvPolynomial.induction_on' with
  | add f g ihf ihg =>
    rw [map_add, map_add, ihf, ihg, map_add, map_add]
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    have hexp : (s - Finsupp.single j (1 : ℕ)) - Finsupp.single i (1 : ℕ)
        = (s - Finsupp.single i (1 : ℕ)) - Finsupp.single j (1 : ℕ) := by
      ext k
      by_cases hki : i = k <;> by_cases hkj : j = k <;>
        simp [Finsupp.sub_apply, Finsupp.single_apply, hki, hkj] <;> omega
    rw [hexp]
    congr 1
    by_cases hij : i = j
    · subst hij; ring
    · have hi : (s - Finsupp.single j (1 : ℕ)) i = s i := by
        have h0 : (Finsupp.single j (1 : ℕ)) i = 0 := by
          simp [Finsupp.single_apply, Ne.symm hij]
        simp [Finsupp.sub_apply, h0]
      have hj : (s - Finsupp.single i (1 : ℕ)) j = s j := by
        have h0 : (Finsupp.single i (1 : ℕ)) j = 0 := by
          simp [Finsupp.single_apply, hij]
        simp [Finsupp.sub_apply, h0]
      rw [hi, hj]
      ring

/-- One-direction commutation, as a terminating simp normalizer:
`pderiv 1 (pderiv 0 ·)` rewrites to `pderiv 0 (pderiv 1 ·)`, pushing
every `pderiv 1` inward past `pderiv 0`, so mixed partials reach a
unique canonical order. -/
theorem pderiv_comm01 (f : MvPolynomial (Fin 2) ℚ) :
    pderiv (1 : Fin 2) (pderiv (0 : Fin 2) f) =
      pderiv (0 : Fin 2) (pderiv (1 : Fin 2) f) :=
  pderiv_comm 1 0 f

/-- The Poisson bracket on two-variable polynomials over `ℚ`:
`[f,g] = f_x·g_y - f_y·g_x`. -/
noncomputable def pbracket (f g : MvPolynomial (Fin 2) ℚ) : MvPolynomial (Fin 2) ℚ :=
  pderiv (0 : Fin 2) f * pderiv (1 : Fin 2) g -
    pderiv (1 : Fin 2) f * pderiv (0 : Fin 2) g

/-- Antisymmetry: `[f,g] = -[g,f]`. -/
theorem pbracket_antisymm (f g : MvPolynomial (Fin 2) ℚ) :
    pbracket f g = -pbracket g f := by
  simp only [pbracket]
  ring

/-- Additivity in the first argument. -/
theorem pbracket_add_left (f g h : MvPolynomial (Fin 2) ℚ) :
    pbracket (f + g) h = pbracket f h + pbracket g h := by
  simp only [pbracket, map_add]
  ring

/-- Additivity in the second argument. -/
theorem pbracket_add_right (f g h : MvPolynomial (Fin 2) ℚ) :
    pbracket f (g + h) = pbracket f g + pbracket f h := by
  simp only [pbracket, map_add]
  ring

/-- Homogeneity in the first argument (`ℚ`-linearity). -/
theorem pbracket_smul (c : ℚ) (f g : MvPolynomial (Fin 2) ℚ) :
    pbracket (c • f) g = c • pbracket f g := by
  simp only [pbracket, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul]
  ring

/-- Leibniz rule in the first argument:
`[f·g, h] = f·[g,h] + g·[f,h]`. -/
theorem pbracket_leibniz (f g h : MvPolynomial (Fin 2) ℚ) :
    pbracket (f * g) h = f * pbracket g h + g * pbracket f h := by
  simp only [pbracket, MvPolynomial.pderiv_mul]
  ring

/-- Jacobi identity (KERNEL — see header): second derivatives are
normalized by `pderiv_comm01`, then the twelve terms cancel. -/
theorem pbracket_jacobi (f g h : MvPolynomial (Fin 2) ℚ) :
    pbracket (pbracket f g) h + pbracket (pbracket g h) f +
      pbracket (pbracket h f) g = 0 := by
  simp only [pbracket, MvPolynomial.pderiv_mul, map_sub, pderiv_comm01]
  ring

/-- The translation automorphism `φ(x) = x`, `φ(y) = y + μ`
(the polynomial model of the φ in esquina(3)'s argument). -/
noncomputable def phiTranslate (mu : ℚ) :
    MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.aeval ![X 0, X 1 + C mu]

/-- Chain rule for the translation, CONDITIONAL on the `pderiv`/`aeval`
commutation (the exact missing lemma — see header). -/
theorem pbracket_translate (mu : ℚ)
    (hchain : ∀ (i : Fin 2) (f : MvPolynomial (Fin 2) ℚ),
      pderiv i (phiTranslate mu f) = phiTranslate mu (pderiv i f))
    (f g : MvPolynomial (Fin 2) ℚ) :
    pbracket (phiTranslate mu f) (phiTranslate mu g) =
      phiTranslate mu (pbracket f g) := by
  simp only [pbracket, hchain, map_mul, map_sub]

/-- The bracket value in Joseph's counterexample (R9): with
`A = y(x²+1)+x` and `B = x`, `[A,B] = -(x²+1)`. -/
theorem joseph_counterexample_bracket :
    pbracket ((X 1) * ((X 0) ^ 2 + 1) + X 0) (X 0) =
      -((X 0) ^ 2 + 1) := by
  have h00 : pderiv (0 : Fin 2) (X 0 : MvPolynomial (Fin 2) ℚ) = 1 :=
    MvPolynomial.pderiv_X_self 0
  have h11 : pderiv (1 : Fin 2) (X 1 : MvPolynomial (Fin 2) ℚ) = 1 :=
    MvPolynomial.pderiv_X_self 1
  have h01 : pderiv (0 : Fin 2) (X 1 : MvPolynomial (Fin 2) ℚ) = 0 :=
    MvPolynomial.pderiv_X_of_ne (by decide)
  have h10 : pderiv (1 : Fin 2) (X 0 : MvPolynomial (Fin 2) ℚ) = 0 :=
    MvPolynomial.pderiv_X_of_ne (by decide)
  simp only [pbracket, map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_one,
    h00, h11, h01, h10]
  ring
