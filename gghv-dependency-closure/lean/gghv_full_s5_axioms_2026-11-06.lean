/-
  GGHV §5 ("Systems of polynomial equations for (9,24) and (9,27)"), full-proof leg C.
  Paper: arXiv:2204.14178v1, TeX ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.
  Inventory: ~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/gghv_statement_inventory.md
  (entries E10–E17). Scratch deliverable — NO repo commits; incorporation only after the
  validation gate.

  CLAIM: see the per-item verdicts below. STATUS: compiled on lean-build-3 (Lean 4.34.0,
  Mathlib), axioms printed per theorem; no `sorryAx` anywhere in this file.
  Toolchain: Lean 4.34.0, Lake 5.0.0, Singular 4.3.1, SymPy 1.14.0 (all on lean-build-3).

  Per-item verdicts (HLRE v5 grades; KERNEL = kernel-verified on the permitted triple
  [propext, Classical.choice, Quot.sound] or a subset; CONDITIONAL = proved from the named
  premises; BLOCKED = not formalized, blocker stated):
  - E13 (f separable): KERNEL. ODE, C3*f = f1, f = y(y+1)g, deg f = 6, deg g = 4,
    g(0) ≠ 0, g(-1) ≠ 0, Bézout identity, separability — all kernel over ℚ[y].
    Second-tool check (SymPy 1.14.0 + Singular 4.3.1, both rc=0): e13_second_tool_check.log.
  - E16 (9 equations ⇒ principal equation): KERNEL (elimination step). The certificate
    identity is proved by `ring`; the principal equation follows from the 9 equations
    + d_{-1} ≠ 0. The DERIVATION of the 9 equations from the C/F/D expansions is OPEN
    (carried as the link hypothesis in E10's assembly).
  - E14 (D_k ∈ K[y]): CONDITIONAL (kernel induction from the convolution identity,
    carried as a hypothesis; the convolution identity itself is the E11 link).
  - E15 (valuations -39 / 51): kernel arithmetic identities + CONDITIONAL valuation
    bounds (from the E11-derived C_k bounds + monomial valuations, carried).
  - E12 (Remark): PARTIAL — the tilde identities are KERNEL; "(P̃,Q̃) still satisfy
    Thm 5.1" is CONDITIONAL on bracket/face preservation (named premises).
  - E11 (calculo de C): BLOCKED on the Laurent-series library (Mathlib has no ready
    Laurent series with the needed API). KERNEL pieces proved here: the corrected
    recursion step, and the sign-slip lemma showing the paper's as-printed recursion
    gives -P_{6-k} instead of P_{6-k}. The existence of C, F with items (1)–(4) is
    NOT formalized; it is carried as the link hypothesis in E10/E14/E15.
  - E10 (Theorem 5.1): CONDITIONAL assembly — kernel rescaling + endgame applied to
    the §5 data supplied by the link hypothesis (link_924/link_927, §5 rescaling inputs,
    coefficient-system derivation, 9-equation derivation, [GGV1] Props 1.13/2.1).
  - E17 (Corollary 5.2): CONDITIONAL assembly on Thm 5.1 + Cor 7.2 + Thm 2.6 + Def 4.3
    + the ψ sixth-power step (all carried inside the link hypothesis).

  Paper slips found in §5 (flagged, not silently corrected):
  (1) E11 recursion sign error (TeX ~1462–1465): the paper writes
      2C₃C_{3-k} = -P_{6-k} - Σ_{j=1}^{k-1} C_{3-j}C_{3-k+j}, but the expansion of
      (Σ_{i=0}^k C_{3-i}x^{3-i})² at x^{6-k} is 2C₃C_{3-k} + Σ_{j=1}^{k-1}…, which with
      the printed recursion equals -P_{6-k}, contradicting (a_k). Correct:
      C_{3-k} := (1/(2C₃))(P_{6-k} - Σ_{j=1}^{k-1}…). See e11_recursion_sign_slip.
  (2) E11 valuation estimates (TeX 1477, 1493): the paper writes v(C_{3-j}C_{3-k+j})
      ≤ v(C_{3-j}) v(C_{3-k+j}) (product of valuations); it should be the sum.
      The bounds that follow are the sum, so this is a harmless typo.
  (3) E16 (D̃²)_{-7} display (TeX ~1680): contains a literal term `2 d_{-1} 0`.
      Correct expansion (from the (D̃²)_{-k} definition, and as used in the Singular
      elim/cert scripts): 2 d₃d_{-10} + 2 d₂d_{-9} + 2 d₁d_{-8} + 2 d₀d_{-7}
      + 2 d_{-1}d_{-6} + 2 d_{-2}d_{-5} + 2 d_{-3}d_{-4} with d₃=1, d₂=0 (the printed
      term is a slip for the vanishing 2 d₂d_{-9} term). The 9-equation system used
      here is the correct expansion. §5 displays no (D̃²)_{-6} equation; the 9
      equations are 6 D̃² equations (-1,-2,-3,-4,-5,-7) + 3 Q̃ equations (-1,-2,-4).
-/
import Mathlib

open Polynomial
open Finset

/-! ## §1. Helpers: `C`-coefficients against polynomial numerals.

  `ring` / `ring_nf` treat each `C r` as an opaque atom and do not combine
  `C a * C b`; `decide` fails on ℚ[X] equality; `native_decide` is forbidden
  (adds `Lean.ofReduceBool`). The lemmas below combine `C q * n → C (q*n)`
  (and the symmetric forms) so that `norm_num` can evaluate the rational
  arithmetic inside `C (…)`. Note: `rw [C_mul_ofNat']` works where
  `simp only [C_mul_ofNat']` does not fire, so the pipeline below uses
  `repeat rw`. -/

lemma C_mul_ofNat' (q : ℚ) (n : ℕ) [n.AtLeastTwo] :
    C q * (OfNat.ofNat n : ℚ[X]) = C (q * OfNat.ofNat n) := by
  rw [← C_ofNat, ← C_mul]

lemma ofNat_mul_C' (q : ℚ) (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ℚ[X]) * C q = C (OfNat.ofNat n * q) := by
  rw [mul_comm, C_mul_ofNat']; congr 1; ring

lemma C_mul_natCast' (q : ℚ) (n : ℕ) :
    C q * ((n : ℕ) : ℚ[X]) = C (q * (n : ℚ)) := by
  rw [← map_natCast C, ← C_mul]

lemma natCast_mul_C' (q : ℚ) (n : ℕ) :
    ((n : ℕ) : ℚ[X]) * C q = C ((n : ℚ) * q) := by
  rw [mul_comm, C_mul_natCast']; congr 1; ring

/-- Monomial normalizers for the Bézout identity (probe32): `ring_nf` leaves
    monomials with two C-coefficients in several arrangements (C's adjacent or
    separated by X^n, left- or right-nested), and `ring` cannot add distinct
    C-atoms. These normalize every monomial to X^n * C r (single C, X first). -/
lemma C_mul_X_pow_mul_C (a b : ℚ) (n : ℕ) :
    C a * X ^ n * C b = C (a * b) * X ^ n := by
  have h : C a * X ^ n * C b = C a * C b * X ^ n := by ring
  rw [h, ← C_mul]

lemma X_pow_mul_C_mul_C (a b : ℚ) (n : ℕ) :
    X ^ n * C a * C b = X ^ n * C (a * b) := by
  have h : X ^ n * C a * C b = X ^ n * (C a * C b) := by ring
  rw [h, ← C_mul]

lemma C_mul_C_mul_X_pow (a b : ℚ) (n : ℕ) :
    C a * (C b * X ^ n) = C (a * b) * X ^ n := by
  have h : C a * (C b * X ^ n) = (C a * C b) * X ^ n := by ring
  rw [h, ← C_mul]

lemma C_mul_X_pow (a : ℚ) (n : ℕ) : C a * X ^ n = X ^ n * C a := mul_comm _ _

lemma C_mul_X_pow_C (a b : ℚ) (n : ℕ) :
    C a * (X ^ n * C b) = X ^ n * C (a * b) := by
  have h : C a * (X ^ n * C b) = C a * C b * X ^ n := by ring
  rw [h, ← C_mul, C_mul_X_pow]

/-! ## §2. E13 — `f` separable (KERNEL).

  Definitions (all in ℚ[X], coefficients as `C (r : ℚ)`):
  C₃ = y⁸(y+1); f₁ = -(1/910) y⁹(y+1)²(35 - 42y + 54y² - 81y³ + 243y⁴);
  g = -(1/910)(35 - 42y + 54y² - 81y³ + 243y⁴);
  f = -(243/910)y⁶ - (81/455)y⁵ + (27/910)y⁴ - (6/455)y³ + (1/130)y² - (1/26)y.
  Bézout coefficients U, V from the SymPy `gcdex` check (see e13_second_tool_check.log).
  Pipeline for the polynomial identities (verified on the ODE, probe25):
  simp only [defs + derivative lemmas + C-combine lemmas] → norm_num → ring_nf →
  simp only [mul_assoc] → repeat rw [C_mul_ofNat'] → repeat rw [ofNat_mul_C'] →
  repeat rw [C_mul_natCast'] → repeat rw [natCast_mul_C'] → norm_num →
  simp only [C_ofNat, map_one] → ring. -/

noncomputable def e13C3 : ℚ[X] := X ^ 8 * (X + 1)

noncomputable def e13f1 : ℚ[X] := C (-(1 / 910)) * X ^ 9 * (X + 1) ^ 2 *
  (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4)

noncomputable def e13g : ℚ[X] := C (-(1 / 910)) *
  (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4)

noncomputable def e13f : ℚ[X] := C (-(243 / 910)) * X ^ 6 - C (81 / 455) * X ^ 5
  + C (27 / 910) * X ^ 4 - C (6 / 455) * X ^ 3 + C (1 / 130) * X ^ 2 - C (1 / 26) * X

noncomputable def e13U : ℚ[X] := C (600696 / 455) * X ^ 4 + C (339552 / 455) * X ^ 3
  - C (47088 / 455) * X ^ 2 + C (16992 / 455) * X - C (1112 / 65)

noncomputable def e13V : ℚ[X] := -(C (100116 / 455) * X ^ 5) - C (67716 / 455) * X ^ 4
  + C (11448 / 455) * X ^ 3 - C (1032 / 91) * X ^ 2 + C (436 / 65) * X - C 26

/-- E13: derivative of C₃. -/
theorem e13_C3_deriv : derivative e13C3 = (9 * X + 8) * X ^ 7 := by
  simp only [e13C3, derivative_mul, derivative_pow, derivative_add, derivative_X,
    derivative_one, derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul,
    ← mul_add, ← C_add, map_neg, map_one]
  norm_num
  ring_nf

/-- E13: the differential equation for f₁. -/
theorem e13_ode : X ^ 9 * (X + 1) ^ 2
    = 6 * X * (X + 1) * derivative e13f1 - 10 * (9 * X + 8) * e13f1 := by
  simp only [e13C3, e13f1, e13f, e13g, e13U, e13V, derivative_mul, derivative_pow,
    derivative_add, derivative_sub, derivative_C, derivative_X, derivative_one,
    derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul, ← mul_add, ← C_add,
    map_neg, map_one]
  norm_num
  ring_nf
  simp only [mul_assoc]
  repeat rw [C_mul_ofNat']
  repeat rw [ofNat_mul_C']
  repeat rw [C_mul_natCast']
  repeat rw [natCast_mul_C']
  norm_num
  try simp only [C_ofNat, map_one]
  ring

/-- E13: f = y(y+1)g. -/
theorem e13_f_factor : e13f = X * (X + 1) * e13g := by
  simp only [e13C3, e13f1, e13f, e13g, e13U, e13V, derivative_mul, derivative_pow,
    derivative_add, derivative_sub, derivative_C, derivative_X, derivative_one,
    derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul, ← mul_add, ← C_add,
    map_neg, map_one]
  norm_num
  ring_nf
  simp only [mul_assoc]
  repeat rw [C_mul_ofNat']
  repeat rw [ofNat_mul_C']
  repeat rw [C_mul_natCast']
  repeat rw [natCast_mul_C']
  norm_num
  try simp only [C_ofNat, map_one]
  ring

/-- E13: C₃·f = f₁ (so f = C₃²F_{-4} with C₃ = y⁸(y+1)).
    Proved in factored form via `e13_f_factor`: both sides are the same product
    of atoms, so `ring` closes it with no coefficient arithmetic. -/
theorem e13_C3_mul_f : e13C3 * e13f = e13f1 := by
  rw [e13_f_factor]
  simp only [e13C3, e13g, e13f1]
  ring


/-- E13: deg f = 6. -/
theorem e13_f_natDegree : e13f.natDegree = 6 := by
  unfold e13f
  compute_degree <;> norm_num

/-- E13: deg g = 4. (The outer `C (-(1/910))` factor defeats `compute_degree`
    directly, so split it off with `natDegree_mul` and compute the inner degree.) -/
theorem e13_g_natDegree : e13g.natDegree = 4 := by
  have h1 : (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4 : ℚ[X]).natDegree
      = 4 := by
    compute_degree <;> norm_num
  have hne : (C 35 - C 42 * X + C 54 * X ^ 2 - C 81 * X ^ 3 + C 243 * X ^ 4 : ℚ[X]) ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  unfold e13g
  rw [Polynomial.natDegree_mul (C_ne_zero.mpr (by norm_num)) hne, h1,
    Polynomial.natDegree_C]

/-- E13: g(0) = -1/26 ≠ 0. -/
theorem e13_g_ne_zero_at_zero : eval 0 e13g ≠ 0 := by
  unfold e13g
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X]
  norm_num

/-- E13: g(-1) = -1/2 ≠ 0 (so (y+1) ∤ g). -/
theorem e13_g_ne_zero_at_neg_one : eval (-1) e13g ≠ 0 := by
  unfold e13g
  simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X]
  norm_num

/-- E13: Bézout identity U·f + V·f′ = 1 (coefficients from SymPy `gcdex`). -/
theorem e13_bezout : e13U * e13f + e13V * derivative e13f = 1 := by
  simp only [e13C3, e13f1, e13f, e13g, e13U, e13V, derivative_mul, derivative_pow,
    derivative_add, derivative_sub, derivative_C, derivative_X, derivative_one,
    derivative_ofNat, C_ofNat, C_eq_natCast, ← C_mul, ← add_mul, ← mul_add, ← C_add,
    map_neg, map_one]
  norm_num
  ring_nf
  simp only [mul_assoc]
  repeat rw [C_mul_ofNat']
  repeat rw [ofNat_mul_C']
  repeat rw [C_mul_natCast']
  repeat rw [natCast_mul_C']
  norm_num
  -- Combine the C-coefficients (probe32): `ring_nf` leaves products `C a * C b`
  -- and sums of like monomials with different C-coefficients, which `ring`
  -- treats as distinct atoms. First normalize every monomial to X^n * C r,
  -- turn subtractions into additions of negations, push the negation inside C,
  -- right-associate the sum, then factor out the common X-power and combine the
  -- C's (C is a ring hom). `ring_nf` then cancels the identical-atom pairs
  -- (each X^5..X^10 monomial appears twice with the same C-atom and opposite
  -- signs, the U·f and V·f′ contributions); only the X^1 terms (distinct
  -- C-atoms) survive, and a second combining pass finishes them (`ring_nf`
  -- leaves the goal in HSub form, so `← mul_sub`/`← C_sub` do the work).
  simp only [C_mul_X_pow_mul_C, X_pow_mul_C_mul_C, C_mul_C_mul_X_pow, C_mul_X_pow_C,
    ← C_mul, C_mul_X_pow]
  simp only [sub_eq_add_neg, ← mul_neg, ← map_neg]
  simp only [add_assoc, ← mul_add, ← mul_sub, ← C_add, ← C_sub]
  norm_num
  ring_nf
  simp only [C_mul_X_pow, ← mul_neg, ← map_neg, ← mul_add, ← mul_sub, ← C_add,
    ← C_sub]
  norm_num
  try ring

/-- E13: f is separable. -/
theorem e13_f_separable : e13f.Separable := by
  rw [Polynomial.separable_def']
  exact ⟨e13U, e13V, e13_bezout⟩

/-! ## §3. E16 — the 9-equation system implies the principal equation (KERNEL).

  The certificate identity below is transcribed verbatim from
  `d1_singular_cert_s5_2026-11-05.sing` (Singular verifies CERT_DIFF = 0).
  The 9 equations are the 6 D̃² equations (-1,-2,-3,-4,-5,-7) + the 3 Q̃ equations
  (-1,-2,-4), in the CORRECT expansion (see the (D̃²)_{-7} slip note in the header).
  The derivation of the 9 equations from the C/F/D expansions is OPEN — only the
  elimination step (9 equations ⇒ principal equation) is proved here. -/

/-- E16 certificate identity: d_{-1} * (principal equation) = combination of the
    9 equations. Proved by `ring` (integer coefficients, no `C`'s). -/
theorem e16_cert {R : Type*} [CommRing R]
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F : R) :
    dm1 * (18 * C3 ^ 23 * F * d1 * dm1 ^ 6 + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9)
    = (-12 * C3 ^ 46 * F ^ 2 * d0 ^ 2 * dm1 - 12 * C3 ^ 46 * F ^ 2 * d1 * dm1 ^ 2
        - 12 * C3 ^ 46 * F ^ 2 * dm1 * dm3 - 18 * C3 ^ 23 * F * d0 ^ 2 * dm1 ^ 3 * dm2
        - 18 * C3 ^ 23 * F * d1 * dm1 ^ 4 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 * dm3
        - 27 * d0 ^ 2 * d1 * dm1 ^ 7 - 27 * d0 ^ 2 * dm1 ^ 5 * dm2 ^ 2
        - 27 * d0 * dm1 ^ 7 * dm2 - 27 * d1 ^ 2 * dm1 ^ 8 - 27 * d1 * dm1 ^ 7 * dm3
        - 27 * d1 * dm1 ^ 6 * dm2 ^ 2 + 27 * dm1 ^ 9 - 27 * dm1 ^ 5 * dm2 ^ 2 * dm3)
      * (2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4)
    + (-24 * C3 ^ 46 * F ^ 2 * d0 * d1 * dm1 - 12 * C3 ^ 46 * F ^ 2 * dm1 * dm2
        - 36 * C3 ^ 23 * F * d0 * d1 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 ^ 2
        - 54 * d0 * d1 ^ 2 * dm1 ^ 7 - 54 * d0 * d1 * dm1 ^ 5 * dm2 ^ 2
        + 27 * d0 * dm1 ^ 8 - 54 * d1 * dm1 ^ 7 * dm2 - 27 * dm1 ^ 5 * dm2 ^ 3)
      * (dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5)
    + (-12 * C3 ^ 46 * F ^ 2 * d1 ^ 2 * dm1 - 12 * C3 ^ 46 * F ^ 2 * dm1 ^ 2
        - 18 * C3 ^ 23 * F * d1 ^ 2 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 4 * dm2
        - 27 * d1 ^ 3 * dm1 ^ 7 - 27 * d1 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 27 * dm1 ^ 6 * dm2 ^ 2)
      * (2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6)
    + (-24 * C3 ^ 46 * F ^ 2 * d0 * dm1 - 36 * C3 ^ 23 * F * d0 * dm1 ^ 3 * dm2
        - 54 * d0 * d1 * dm1 ^ 7 - 54 * d0 * dm1 ^ 5 * dm2 ^ 2 - 27 * dm1 ^ 7 * dm2)
      * (dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7)
    + (-24 * C3 ^ 46 * F ^ 2 * d1 * dm1 - 36 * C3 ^ 23 * F * d1 * dm1 ^ 3 * dm2
        - 54 * d1 ^ 2 * dm1 ^ 7 - 54 * d1 * dm1 ^ 5 * dm2 ^ 2 + 27 * dm1 ^ 8)
      * (2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8)
    + (-12 * C3 ^ 46 * F ^ 2 * dm1 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2
        - 27 * d1 * dm1 ^ 7 - 27 * dm1 ^ 5 * dm2 ^ 2)
      * (2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7
        + 2 * d1 * dm8)
    + (8 * C3 ^ 46 * F ^ 2 * d0 * dm1 + 12 * C3 ^ 23 * F * d0 * dm1 ^ 3 * dm2
        + 18 * d0 * d1 * dm1 ^ 7 + 18 * d0 * dm1 ^ 5 * dm2 ^ 2 + 18 * dm1 ^ 7 * dm2)
      * (3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2
        + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7)
    + (8 * C3 ^ 46 * F ^ 2 * d1 * dm1 + 12 * C3 ^ 23 * F * d1 * dm1 ^ 3 * dm2
        + 18 * d1 ^ 2 * dm1 ^ 7 + 18 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * dm1 ^ 8)
      * (3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3
        + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6
        + 3 * dm8)
    + (8 * C3 ^ 46 * F ^ 2 * dm1 + 12 * C3 ^ 23 * F * dm1 ^ 3 * dm2
        + 18 * d1 * dm1 ^ 7 + 18 * dm1 ^ 5 * dm2 ^ 2)
      * (3 * dm10 + 3 * dm1 ^ 2 * dm2 + 3 * d0 * dm2 ^ 2 + 6 * d0 * dm1 * dm3
        + 6 * d1 * dm2 * dm3 + 3 * d0 ^ 2 * dm4 + 6 * d1 * dm1 * dm4 + 6 * dm3 * dm4
        + 6 * d0 * d1 * dm5 + 6 * dm2 * dm5 + 3 * d1 ^ 2 * dm6 + 6 * dm1 * dm6
        + 6 * d0 * dm7 + 6 * d1 * dm8 + F * C3 ^ 23) := by
  ring

/-- E16 principal equation (kernel): from the 9 equations and d_{-1} ≠ 0. -/
theorem e16_principal {R : Type*} [Field R]
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F : R)
    (hD1 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD2 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD3 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD4 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD5 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD7 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7
      + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2
      + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3
      + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6
      + 3 * dm8 = 0)
    (hQ4 : 3 * dm10 + 3 * dm1 ^ 2 * dm2 + 3 * d0 * dm2 ^ 2 + 6 * d0 * dm1 * dm3
      + 6 * d1 * dm2 * dm3 + 3 * d0 ^ 2 * dm4 + 6 * d1 * dm1 * dm4 + 6 * dm3 * dm4
      + 6 * d0 * d1 * dm5 + 6 * dm2 * dm5 + 3 * d1 ^ 2 * dm6 + 6 * dm1 * dm6
      + 6 * d0 * dm7 + 6 * d1 * dm8 + F * C3 ^ 23 = 0)
    (hdm1 : dm1 ≠ 0) :
    18 * C3 ^ 23 * F * d1 * dm1 ^ 6 + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9 = 0 := by
  have h := e16_cert d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F
  rw [hD1, hD2, hD3, hD4, hD5, hD7, hQ1, hQ2, hQ4] at h
  simp only [mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hdm1

/-! ## §4. E14 — D_k ∈ K[y] (CONDITIONAL).

  ℕ-indexed from the top: D_{2-n} = c n * C3^(2n+1) with only natural exponents.
  The convolution identity `p n = 2*C3*c n + Σ_{m<n} c m * c (n-1-m)` is the
  C² = P coefficient relation, carried as a hypothesis (its proof from E11(1) is
  the E11 link). S is the subring of K playing the role of K[y]; (1/2 : K) ∈ S is
  needed since the recurrence divides by 2. -/

theorem e14_d_mem {K : Type*} [Field K] [CharZero K] {S : Subring K}
    (hhalf : (1 / 2 : K) ∈ S) (C3 : K) (hC3 : C3 ∈ S) (c p : ℕ → K)
    (hp : ∀ n, p n ∈ S)
    (hconv : ∀ n, p n = 2 * C3 * c n + ∑ m ∈ Finset.range n, c m * c (n - 1 - m))
    (n : ℕ) : (c n * C3 ^ (2 * n + 1)) ∈ S := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key : p n * C3 ^ (2 * n)
        = 2 * (c n * C3 ^ (2 * n + 1))
          + ∑ m ∈ Finset.range n,
            (c m * C3 ^ (2 * m + 1)) * (c (n - 1 - m) * C3 ^ (2 * (n - 1 - m) + 1)) := by
      rw [hconv n, add_mul, Finset.sum_mul]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro m hm
        have hm' : m < n := Finset.mem_range.mp hm
        have hexp : 2 * m + 1 + (2 * (n - 1 - m) + 1) = 2 * n := by omega
        have hC3pow : C3 ^ (2 * n) = C3 ^ (2 * m + 1) * C3 ^ (2 * (n - 1 - m) + 1) := by
          rw [← pow_add, hexp]
        rw [hC3pow]
        ring
    have hsum : (∑ m ∈ Finset.range n,
        (c m * C3 ^ (2 * m + 1)) * (c (n - 1 - m) * C3 ^ (2 * (n - 1 - m) + 1))) ∈ S := by
      apply sum_mem
      intro m hm
      have hm' : m < n := Finset.mem_range.mp hm
      apply S.mul_mem
      · exact ih m hm'
      · exact ih (n - 1 - m) (by omega)
    have hpn : p n * C3 ^ (2 * n) ∈ S := S.mul_mem (hp n) (S.pow_mem hC3 _)
    have hd : c n * C3 ^ (2 * n + 1)
        = (1 / 2 : K) * (p n * C3 ^ (2 * n)
          - ∑ m ∈ Finset.range n,
            (c m * C3 ^ (2 * m + 1)) * (c (n - 1 - m) * C3 ^ (2 * (n - 1 - m) + 1))) := by
      rw [key]
      ring
    rw [hd]
    apply S.mul_mem hhalf
    exact S.sub_mem hpn hsum

/-! ## §5. E15 — valuations v_{-13,-1}(D) = -39, v_{17,1}(D) = 51.

  Kernel arithmetic identities (the paper's TeX 1707–1710 and 1721–1724) plus
  CONDITIONAL valuation bounds: an abstract directed valuation `v` (the properties
  of v_{ρ,σ} the argument uses), the E11-derived C_k bounds, and the x-monomial
  valuations (passed as explicit ℤ hypotheses, since the x-monomials live in the
  Laurent ring, not in R). The paper's v_{ρ,σ} is the MAXIMUM over monomials
  (the (ρ,σ)-degree), which is what makes v(C₃) = -8 resp. 9. -/

/-- Abstract directed valuation (the properties of v_{ρ,σ} that E15's argument uses). -/
structure ValData (R : Type*) [CommRing R] where
  v : R → ℤ
  v_one : v 1 = 0
  v_mul : ∀ a b, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b

theorem pow_ne_zero_of_ne {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (a : R) (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_ne_zero
  | succ n ih => rw [pow_succ]; exact mul_ne_zero ih ha

theorem val_pow {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R] (V : ValData R)
    (a : R) (n : ℕ) (ha : a ≠ 0) :
    V.v (a ^ n) = (n : ℤ) * V.v a := by
  induction n with
  | zero => rw [pow_zero, V.v_one]; simp
  | succ n ih =>
    rw [pow_succ, V.v_mul _ _ (pow_ne_zero_of_ne a ha n) ha, ih]
    push_cast
    ring

/-- E15 arithmetic identity (kernel): the (-13,-1) bound is constant in k. -/
theorem e15_arith_neg13 (k : ℤ) : -16 * k + 1 + (5 - 2 * k) * (-8) = -39 := by ring

/-- E15 arithmetic identity (kernel): the (17,1) bound is constant in k. -/
theorem e15_arith_17 (k : ℤ) : 18 * k + 6 + (5 - 2 * k) * 9 = 51 := by ring

/-- E15 (-13,-1) bound (conditional): in ℕ-indexed form (k = 2 - n), if the
    C-coefficient bound v(C_{2-n}) ≤ 3n - 5 (from E11(3): lowest y-power of C_k
    is ≥ y^{3k-1}), v(C3) = -8, and the x-monomial contributes hxv = 13n - 26,
    then v(D_{2-n} x^{2-n}) ≤ -39. -/
theorem e15_bound_neg13 {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (V : ValData R)
    (C3 : R) (c : ℕ → R) (n : ℕ)
    (hC3 : C3 ≠ 0) (hC3v : V.v C3 = -8)
    (hcn : c n ≠ 0)
    (hC : V.v (c n) ≤ 3 * (n : ℤ) - 5)
    (hxv : ℤ) (hhxv : hxv = 13 * (n : ℤ) - 26) :
    V.v (c n * C3 ^ (2 * n + 1)) + hxv ≤ -39 := by
  have h1 : V.v (c n * C3 ^ (2 * n + 1))
      = V.v (c n) + (2 * (n : ℤ) + 1) * V.v C3 := by
    rw [V.v_mul _ _ hcn (pow_ne_zero_of_ne C3 hC3 _), val_pow V C3 _ hC3]
    push_cast
    ring
  rw [h1, hC3v, hhxv]
  omega

/-- E15 (17,1) bound (conditional): if v(C_{2-n}) ≤ 8 - n (from E11(4): highest
    y-power of C_k is ≤ y^{k+6}), v(C3) = 9, and the x-monomial contributes
    hxv = 34 - 17n, then v(D_{2-n} x^{2-n}) ≤ 51. -/
theorem e15_bound_17 {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (V : ValData R)
    (C3 : R) (c : ℕ → R) (n : ℕ)
    (hC3 : C3 ≠ 0) (hC3v : V.v C3 = 9)
    (hcn : c n ≠ 0)
    (hC : V.v (c n) ≤ 8 - (n : ℤ))
    (hxv : ℤ) (hhxv : hxv = 34 - 17 * (n : ℤ)) :
    V.v (c n * C3 ^ (2 * n + 1)) + hxv ≤ 51 := by
  have h1 : V.v (c n * C3 ^ (2 * n + 1))
      = V.v (c n) + (2 * (n : ℤ) + 1) * V.v C3 := by
    rw [V.v_mul _ _ hcn (pow_ne_zero_of_ne C3 hC3 _), val_pow V C3 _ hC3]
    push_cast
    ring
  rw [h1, hC3v, hhxv]
  omega

/-! ## §6. E12 — Remark (PARTIAL).

  The tilde transformation: P̃ = P + (2/3)α₁, Q̃ = Q - α₂P - α₀, with
  P = C² and Q = C³ + α₂C² + α₁C + α₀ + α_{-1}C⁻¹ + F. The two algebraic
  identities are KERNEL; the claim that (P̃,Q̃) still satisfy Thm 5.1 is
  CONDITIONAL on bracket preservation and face preservation (named premises
  `hJac`, `hFace` — the bracket computation and the vertex check are not
  formalized here). -/

/-- E12: Q̃ = C³ + α₁C + λC⁻¹ + F with λ := α_{-1} (kernel, pure `ring`). -/
theorem e12_Qtilde {K : Type*} [Field K] [CharZero K] {C F α2 α1 α0 αm1 : K}
    {P Q : K} (hP : P = C ^ 2)
    (hQ : Q = C ^ 3 + α2 * C ^ 2 + α1 * C + α0 + αm1 * C⁻¹ + F) :
    (Q - α2 * P - α0) = C ^ 3 + α1 * C + αm1 * C⁻¹ + F := by
  rw [hQ, hP]; ring

/-- E12: the first correction to C̃² (kernel). -/
theorem e12_Ctilde_sq {K : Type*} [Field K] [CharZero K] {C α1 : K} (hC : C ≠ 0) {P : K}
    (hP : P = C ^ 2) :
    (C + (1 / 3) * α1 * C⁻¹) ^ 2
      = (P + (2 / 3) * α1) + (α1 ^ 2 / 9) * C⁻¹ ^ 2 := by
  rw [hP]; field_simp; ring

/-- E12 Remark, conditional: the tilde pair has Q̃ in the required form (with
    λ = α_{-1}) and satisfies Thm 5.1's conditions, given bracket preservation
    (`hJac`) and face preservation (`hFace`). -/
theorem e12_remark_conditional {K : Type*} [Field K] [CharZero K]
    {C F α2 α1 α0 αm1 : K} (hC : C ≠ 0)
    {P Q : K} (hP : P = C ^ 2)
    (hQ : Q = C ^ 3 + α2 * C ^ 2 + α1 * C + α0 + αm1 * C⁻¹ + F)
    (JacCond FaceCond : K → K → Prop)
    (hJac : JacCond (P + (2 / 3) * α1) (Q - α2 * P - α0))
    (hFace : FaceCond (P + (2 / 3) * α1) (Q - α2 * P - α0)) :
    ∃ lam : K, (Q - α2 * P - α0) = C ^ 3 + α1 * C + lam * C⁻¹ + F
      ∧ JacCond (P + (2 / 3) * α1) (Q - α2 * P - α0)
      ∧ FaceCond (P + (2 / 3) * α1) (Q - α2 * P - α0) := by
  refine ⟨αm1, ?_, hJac, hFace⟩
  exact e12_Qtilde hP hQ

/-! ## §7. E11 — calculo de C (BLOCKED on the Laurent-series library).

  The Laurent series C, F and items (1)–(4) of Proposition `calculo de C` are NOT
  formalized: Mathlib has no ready Laurent series with the needed API (a D2
  INTERFACE gap). What IS proved here, kernel, is the recursion algebra:
  with c j := C_{3-j} and p k := P_{6-k}, the CORRECTED recursion yields the
  coefficient identity Σ_{j=0}^k C_{3-j}C_{3-k+j} = P_{6-k}, while the paper's
  AS-PRINTED recursion yields -P_{6-k} (a genuine sign error, TeX ~1462–1465).
  The valuation estimates' product-vs-sum typo (TeX 1477, 1493) is also flagged
  in the header; the corrected bounds are the E15 arithmetic (kernel). -/

/-- E11 recursion step (kernel, corrected sign). -/
theorem e11_recursion_step {R : Type*} [Field R] [CharZero R] {C3 : R} (hC3 : C3 ≠ 0)
    (c p : ℕ → R) (k : ℕ) (hk : 1 ≤ k) (hc0 : c 0 = C3)
    (hrec : c k = (2 * C3)⁻¹ * (p k - ∑ j ∈ Finset.range (k - 1), c (j + 1) * c (k - 1 - j))) :
    ∑ j ∈ Finset.range (k + 1), c j * c (k - j) = p k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrec
  have h2C3 : (2 * C3 : R) ≠ 0 := mul_ne_zero two_ne_zero hC3
  have hsplit : ∑ j ∈ Finset.range (k' + 1 + 1), c j * c (k' + 1 - j)
      = c 0 * c (k' + 1) + (∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))
        + c (k' + 1) * c 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.sub_self]
    rw [add_comm (∑ j ∈ Finset.range k', c (j + 1) * c (k' + 1 - (j + 1))) (c 0 * c (k' + 1))]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hij : k' + 1 - (j + 1) = k' - j := by omega
    rw [hij]
  have key : (2 * C3) * ((2 * C3)⁻¹
      * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j)))
      = p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j) := by
    rw [← mul_assoc, mul_inv_cancel₀ h2C3, one_mul]
  have h2 : C3 * ((2 * C3)⁻¹
        * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j)))
      + ((2 * C3)⁻¹
        * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))) * C3
      = p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j) := by
    have h3 : C3 * ((2 * C3)⁻¹
          * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j)))
        + ((2 * C3)⁻¹
          * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))) * C3
        = (2 * C3) * ((2 * C3)⁻¹
          * (p (k' + 1) - ∑ j ∈ Finset.range k', c (j + 1) * c (k' - j))) := by ring
    rw [h3, key]
  rw [hsplit, hc0, hrec]
  linear_combination h2

/-- E11 sign slip (kernel): the paper's as-printed recursion yields -P_{6-k}. -/
theorem e11_recursion_sign_slip {R : Type*} [Field R] [CharZero R] {C3 : R} (hC3 : C3 ≠ 0)
    (c p : ℕ → R) (k : ℕ) (hk : 1 ≤ k) (hc0 : c 0 = C3)
    (hrec : c k = -(2 * C3)⁻¹ * (p k + ∑ j ∈ Finset.range (k - 1), c (j + 1) * c (k - 1 - j))) :
    ∑ j ∈ Finset.range (k + 1), c j * c (k - j) = -(p k) := by
  have hrec' : c k = (2 * C3)⁻¹
      * ((-p k) - ∑ j ∈ Finset.range (k - 1), c (j + 1) * c (k - 1 - j)) := by
    rw [hrec]; ring
  exact e11_recursion_step hC3 c (fun n => -p n) k hk hc0 hrec'

/-! ## §8. E10 — Theorem 5.1 (CONDITIONAL assembly).

  Kernel pieces proved here: the clearing lemma (principal equation ⇒ cleared
  form, general commutative ring), the rescaling lemma (cleared equation ⇒ nueva
  ecuacion principal, by factoring y^507(y+1)^6), the tilde-degree bound, and the
  endgame (nueva equation + d̃_{-1} = (y+1)^k + degree bounds + g(-1) ≠ 0 ⇒ False,
  splitting k ≥ 8 by divisibility vs k ≤ 7 by degrees).
  The assembly `thm51_conditional` applies these kernel lemmas to the §5 data
  supplied by the link hypothesis; the link's proof is the open part
  (link_924 / link_927, §5 rescaling inputs, coefficient-system derivation,
  9-equation derivation, [GGV1] Props 1.13/2.1). The g-facts are NOT part of the
  link: they are the kernel E13 results, transported here by cancelling y(y+1). -/

/-- E10 clearing lemma (kernel, general commutative ring): multiplying the principal
    equation by C3^6 and using C3^2 * F = f gives the cleared (all-polynomial) form.
    The step from the paper's F_{-4} (in K[y, C3^{-1}]) to this cleared form is the
    one carried piece here; the algebra below is kernel. -/
theorem e10_clearing {R : Type*} [CommRing R] {C3 F f d1 dm1 d0 : R}
    (hF : C3 ^ 2 * F = f) :
    C3 ^ 6 * (18 * C3 ^ 23 * d1 * dm1 ^ 6 * F + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9)
      = 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3 + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by
  have e1 : C3 ^ 29 * F = C3 ^ 27 * f := by rw [← hF]; ring
  have e3 : C3 ^ 75 * F ^ 3 = C3 ^ 69 * f ^ 3 := by rw [← hF]; ring
  calc C3 ^ 6 * (18 * C3 ^ 23 * d1 * dm1 ^ 6 * F + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9)
      = 18 * (C3 ^ 29 * F) * d1 * dm1 ^ 6 + 8 * (C3 ^ 75 * F ^ 3)
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by ring
    _ = 18 * (C3 ^ 27 * f) * d1 * dm1 ^ 6 + 8 * (C3 ^ 69 * f ^ 3)
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by rw [e1, e3]
    _ = 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9 := by ring

-- The rescaling `ring` (degree-555 identity) needs more recursion depth / heartbeats.
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- E10 rescaling lemma (kernel over ℚ[y]): from the cleared principal equation and the
    substitutions C3 = y^8(y+1), f = y(y+1)g, d1 = y^26 d̃1, d0 = y^39 d̃0,
    d_{-1} = y^52 d̃_{-1}, derive the nueva ecuacion principal by factoring out
    y^507 (y+1)^6 (a non-zero polynomial, so cancellation is valid). -/
theorem e10_rescaling (C3 f d1 d0 dm1 dt1 dt0 dtm1 g : ℚ[X])
    (hC3 : C3 = X ^ 8 * (X + 1)) (hf : f = X * (X + 1) * g)
    (hd1 : d1 = X ^ 26 * dt1) (hd0 : d0 = X ^ 39 * dt0) (hdm1 : dm1 = X ^ 52 * dtm1)
    (hprinc : 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
      + 27 * C3 ^ 6 * d0 * dm1 ^ 9 = 0) :
    18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 8 * (X + 1) ^ 66 * g ^ 3
      + 27 * dt0 * dtm1 ^ 9 = 0 := by
  have hfac : 18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
        + 27 * C3 ^ 6 * d0 * dm1 ^ 9
      = X ^ 555 * (X + 1) ^ 6 * (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g
        + 8 * (X + 1) ^ 66 * g ^ 3 + 27 * dt0 * dtm1 ^ 9) := by
    rw [hC3, hf, hd1, hd0, hdm1]; ring
  rw [hfac] at hprinc
  have hne : (X ^ 555 * (X + 1) ^ 6 : ℚ[X]) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero 555 Polynomial.X_ne_zero
    · apply pow_ne_zero 6
      rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
      exact Polynomial.X_add_C_ne_zero 1
  exact (mul_eq_zero.mp hprinc).resolve_left hne

/-- Degree bound for a tilde coefficient (kernel): from d = y^m * d̃ and deg d ≤ B,
    deg d̃ ≤ B - m. (Used to get deg d̃1 ≤ 8, deg d̃0 ≤ 12 from the paper's cota
    deg d1 ≤ 34, deg d0 ≤ 51.) -/
theorem e10_dt_bound {m B : ℕ} {d dt : ℚ[X]} (hd : d = X ^ m * dt) (hB : d.natDegree ≤ B) :
    dt.natDegree ≤ B - m := by
  by_cases hdt : dt = 0
  · simp [hdt]
  · have h1 : d.natDegree = m + dt.natDegree := by
      rw [hd, Polynomial.natDegree_mul (pow_ne_zero m Polynomial.X_ne_zero) hdt,
        Polynomial.natDegree_pow, Polynomial.natDegree_X]
      omega
    omega

/-- E10 endgame (kernel over ℚ[y]): from the nueva ecuacion principal, d̃_{-1} = (y+1)^k,
    the degree bounds deg d̃1 ≤ 8, deg d̃0 ≤ 12, and g of degree 4 with g(-1) ≠ 0,
    derive False, splitting on k ≥ 8 (divisibility) vs k ≤ 7 (degrees). -/
theorem e10_endgame (dt1 dt0 dtm1 g : ℚ[X]) (k : ℕ)
    (hnueva : 18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 8 * (X + 1) ^ 66 * g ^ 3
      + 27 * dt0 * dtm1 ^ 9 = 0)
    (hdtm1 : dtm1 = (X + 1) ^ k)
    (hdt1 : dt1.natDegree ≤ 8) (hdt0 : dt0.natDegree ≤ 12)
    (hg_deg : g.natDegree = 4) (hg_ne0 : g ≠ 0)
    (hg_neg1 : eval (-1) g ≠ 0) : False := by
  have hX1ne : (X + 1 : ℚ[X]) ≠ 0 := by
    rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
    exact Polynomial.X_add_C_ne_zero 1
  have hX1deg : (X + 1 : ℚ[X]).natDegree = 1 := by
    rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
    exact Polynomial.natDegree_X_add_C 1
  have h8ne : (8 : ℚ[X]) ≠ 0 := by
    rw [← C_ofNat]; exact C_ne_zero.mpr (by norm_num)
  have h80 : (8 : ℚ[X]).natDegree = 0 := by
    rw [← C_ofNat]; exact Polynomial.natDegree_C 8
  have h180 : (18 : ℚ[X]).natDegree = 0 := by
    rw [← C_ofNat]; exact Polynomial.natDegree_C 18
  have h270 : (27 : ℚ[X]).natDegree = 0 := by
    rw [← C_ofNat]; exact Polynomial.natDegree_C 27
  have hteq : (8 * (X + 1) ^ 66 * g ^ 3 : ℚ[X])
      = -(18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 27 * dt0 * dtm1 ^ 9) := by
    linear_combination hnueva
  rcases lt_or_ge k 8 with hk | hk
  · -- k ≤ 7: degree argument. deg term2 = 78, deg (term1 + term3) ≤ 76.
    have ht2 : (8 * (X + 1) ^ 66 * g ^ 3 : ℚ[X]).natDegree = 78 := by
      have h1 : ((8 : ℚ[X]) * (X + 1) ^ 66).natDegree = 66 := by
        rw [Polynomial.natDegree_mul h8ne (pow_ne_zero 66 hX1ne),
          Polynomial.natDegree_pow, hX1deg, h80]
      rw [Polynomial.natDegree_mul (mul_ne_zero h8ne (pow_ne_zero 66 hX1ne))
          (pow_ne_zero 3 hg_ne0), h1, Polynomial.natDegree_pow, hg_deg]
    have hk7 : ((X + 1) ^ k : ℚ[X]).natDegree ≤ 7 := by
      have h' := Polynomial.natDegree_pow_le (p := (X + 1 : ℚ[X])) (n := k)
      rw [hX1deg] at h'
      calc ((X + 1) ^ k : ℚ[X]).natDegree ≤ k * 1 := h'
        _ = k := Nat.mul_one k
        _ ≤ 7 := by omega
    have ht1 : (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g : ℚ[X]).natDegree ≤ 76 := by
      rw [hdtm1]
      have b1 : ((18 : ℚ[X]) * (X + 1) ^ 22).natDegree ≤ 22 := by
        have h := Polynomial.natDegree_mul_le (p := (18 : ℚ[X])) (q := ((X + 1) ^ 22))
        have h22 : (((X + 1) ^ 22 : ℚ[X])).natDegree = 22 := by
          rw [Polynomial.natDegree_pow, hX1deg]
        rw [h180, h22] at h
        exact h
      have b2 : ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1).natDegree ≤ 30 := by
        have h := Polynomial.natDegree_mul_le (p := ((18 : ℚ[X]) * (X + 1) ^ 22)) (q := dt1)
        exact le_trans h (Nat.add_le_add b1 hdt1)
      have b3 : ((((X + 1) ^ k) ^ 6 : ℚ[X])).natDegree ≤ 42 := by
        have h := Polynomial.natDegree_pow_le (p := ((X + 1) ^ k : ℚ[X])) (n := 6)
        calc ((((X + 1) ^ k) ^ 6 : ℚ[X])).natDegree ≤ 6 * ((X + 1) ^ k).natDegree := h
          _ ≤ 6 * 7 := Nat.mul_le_mul (le_refl 6) hk7
          _ = 42 := rfl
      have b4 : ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1 * ((X + 1) ^ k) ^ 6).natDegree ≤ 72 := by
        have h := Polynomial.natDegree_mul_le (p := ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1))
          (q := (((X + 1) ^ k) ^ 6))
        exact le_trans h (Nat.add_le_add b2 b3)
      have h := Polynomial.natDegree_mul_le
        (p := ((18 : ℚ[X]) * (X + 1) ^ 22 * dt1 * ((X + 1) ^ k) ^ 6)) (q := g)
      rw [hg_deg] at h
      exact le_trans h (Nat.add_le_add b4 (le_refl 4))
    have ht3 : (27 * dt0 * dtm1 ^ 9 : ℚ[X]).natDegree ≤ 75 := by
      rw [hdtm1]
      have b1 : ((27 : ℚ[X]) * dt0).natDegree ≤ 12 := by
        have h := Polynomial.natDegree_mul_le (p := (27 : ℚ[X])) (q := dt0)
        rw [h270] at h
        exact le_trans h (Nat.add_le_add (le_refl 0) hdt0)
      have b2 : ((((X + 1) ^ k) ^ 9 : ℚ[X])).natDegree ≤ 63 := by
        have h := Polynomial.natDegree_pow_le (p := ((X + 1) ^ k : ℚ[X])) (n := 9)
        calc ((((X + 1) ^ k) ^ 9 : ℚ[X])).natDegree ≤ 9 * ((X + 1) ^ k).natDegree := h
          _ ≤ 9 * 7 := Nat.mul_le_mul (le_refl 9) hk7
          _ = 63 := rfl
      have h := Polynomial.natDegree_mul_le (p := ((27 : ℚ[X]) * dt0))
        (q := (((X + 1) ^ k) ^ 9))
      exact le_trans h (Nat.add_le_add b1 b2)
    have hsum : (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g + 27 * dt0 * dtm1 ^ 9 :
        ℚ[X]).natDegree ≤ 76 := by
      have h := Polynomial.natDegree_add_le
        (18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g) (27 * dt0 * dtm1 ^ 9)
      omega
    rw [hteq, Polynomial.natDegree_neg] at ht2
    rw [ht2] at hsum
    omega
  · -- k ≥ 8: divisibility argument. (y+1)^70 divides terms 1 and 3, hence term 2;
    -- cancelling (y+1)^66 gives (y+1) | g, contradicting g(-1) ≠ 0.
    have hprime : Prime (X + 1 : ℚ[X]) := by
      have h := Polynomial.prime_X_sub_C (-1 : ℚ)
      have heq : (X - C (-1 : ℚ) : ℚ[X]) = X + 1 := by simp
      rwa [heq] at h
    have hdvd1 : ((X + 1) ^ 70 : ℚ[X]) ∣ 18 * (X + 1) ^ 22 * dt1 * dtm1 ^ 6 * g := by
      rw [hdtm1]
      have e : ((X + 1) ^ (22 + 6 * k) : ℚ[X]) = (X + 1) ^ 22 * (X + 1) ^ (k * 6) := by
        rw [← pow_add]; congr 1; ring
      have hfac : (18 : ℚ[X]) * (X + 1) ^ 22 * dt1 * ((X + 1) ^ k) ^ 6 * g
          = (X + 1) ^ (22 + 6 * k) * (18 * dt1 * g) := by
        rw [← pow_mul, e]; ring
      rw [hfac]
      exact Dvd.dvd.mul_right (pow_dvd_pow (X + 1) (by omega : 70 ≤ 22 + 6 * k)) _
    have hdvd3 : ((X + 1) ^ 70 : ℚ[X]) ∣ 27 * dt0 * dtm1 ^ 9 := by
      rw [hdtm1]
      have e : ((X + 1) ^ (9 * k) : ℚ[X]) = ((X + 1) ^ k) ^ 9 := by
        rw [← pow_mul]; congr 1; ring
      have hfac : (27 : ℚ[X]) * dt0 * ((X + 1) ^ k) ^ 9
          = (X + 1) ^ (9 * k) * (27 * dt0) := by
        rw [← e]; ring
      rw [hfac]
      exact Dvd.dvd.mul_right (pow_dvd_pow (X + 1) (by omega : 70 ≤ 9 * k)) _
    have hdvd2 : ((X + 1) ^ 70 : ℚ[X]) ∣ 8 * (X + 1) ^ 66 * g ^ 3 := by
      rw [hteq]
      exact dvd_neg.mpr (dvd_add hdvd1 hdvd3)
    have h66 : ((X + 1) ^ 66 : ℚ[X]) ≠ 0 := pow_ne_zero 66 hX1ne
    have hdvd4 : ((X + 1) ^ 4 : ℚ[X]) ∣ 8 * g ^ 3 := by
      have e70 : ((X + 1) ^ 70 : ℚ[X]) = (X + 1) ^ 66 * (X + 1) ^ 4 := by rw [← pow_add]
      have h2 : (8 * (X + 1) ^ 66 * g ^ 3 : ℚ[X]) = (X + 1) ^ 66 * (8 * g ^ 3) := by ring
      rw [e70] at hdvd2
      rw [h2] at hdvd2
      exact (mul_dvd_mul_iff_left h66).mp hdvd2
    have hdvd_g3 : ((X + 1) : ℚ[X]) ∣ g ^ 3 := by
      have h14 : ((X + 1) ^ 1 : ℚ[X]) ∣ (X + 1) ^ 4 :=
        pow_dvd_pow (X + 1) (by norm_num)
      rw [pow_one] at h14
      have h1 : ((X + 1) : ℚ[X]) ∣ 8 * g ^ 3 := dvd_trans h14 hdvd4
      rcases hprime.dvd_or_dvd h1 with h8 | hg3
      · exfalso
        have hle := Polynomial.natDegree_le_of_dvd h8 h8ne
        rw [hX1deg, h80] at hle
        omega
      · exact hg3
    have hdvd_g : ((X + 1) : ℚ[X]) ∣ g := hprime.dvd_of_dvd_pow hdvd_g3
    have hroot : (X - C (-1 : ℚ)) ∣ g := by
      have heq : (X - C (-1 : ℚ) : ℚ[X]) = X + 1 := by simp
      rw [heq]; exact hdvd_g
    rw [Polynomial.dvd_iff_isRoot] at hroot
    exact hg_neg1 hroot

/-- E10 Theorem 5.1, CONDITIONAL assembly. `S5Counterexample` is the (opaque)
    existence of a Thm-5.1-shaped counterexample (a (9,24)/(9,27) pair with
    [P,Q] = x + g(y) and the stated Newton data). The link hypothesis packages
    the §5 data a counterexample yields — C3, f, the d's, the tilde d's, g, k —
    including the cleared principal equation and the divisibility/degree bounds;
    its proof is the open part (link_924/link_927, §5 rescaling inputs,
    coefficient-system derivation, 9-equation derivation, [GGV1] Props 1.13/2.1).
    The g-facts are kernel E13 results, transported by cancelling y(y+1). -/
theorem thm51_conditional (S5Counterexample : Prop)
    (link : S5Counterexample →
      ∃ (C3 f d1 d0 dm1 dt1 dt0 dtm1 g : ℚ[X]) (k : ℕ),
        C3 = X ^ 8 * (X + 1) ∧ f = e13f ∧ f = X * (X + 1) * g ∧
        (18 * C3 ^ 27 * d1 * dm1 ^ 6 * f + 8 * C3 ^ 69 * f ^ 3
          + 27 * C3 ^ 6 * d0 * dm1 ^ 9 = 0) ∧
        d1 = X ^ 26 * dt1 ∧ d0 = X ^ 39 * dt0 ∧ dm1 = X ^ 52 * dtm1 ∧
        dt1.natDegree ≤ 8 ∧ dt0.natDegree ≤ 12 ∧ dtm1 = (X + 1) ^ k)
    : ¬ S5Counterexample := by
  intro h
  obtain ⟨C3, f, d1, d0, dm1, dt1, dt0, dtm1, g, k, hC3, hf13, hf, hprinc, hd1, hd0, hdm1,
    hdt1, hdt0, hdtm1⟩ := link h
  have hg_eq : g = e13g := by
    have hXne : (X * (X + 1) : ℚ[X]) ≠ 0 :=
      mul_ne_zero Polynomial.X_ne_zero (by
        rw [show (1 : ℚ[X]) = C 1 from (map_one C).symm]
        exact Polynomial.X_add_C_ne_zero 1)
    have h : X * (X + 1) * g = X * (X + 1) * e13g := by
      rw [← hf, hf13, e13_f_factor]
    exact mul_left_cancel₀ hXne h
  have hg_deg : g.natDegree = 4 := by rw [hg_eq]; exact e13_g_natDegree
  have hg_ne0 : g ≠ 0 := by
    rw [hg_eq]
    intro hg0
    exact e13_g_ne_zero_at_zero (by rw [hg0]; simp)
  have hg_neg1 : eval (-1) g ≠ 0 := by rw [hg_eq]; exact e13_g_ne_zero_at_neg_one
  have hnueva := e10_rescaling C3 f d1 d0 dm1 dt1 dt0 dtm1 g hC3 hf hd1 hd0 hdm1 hprinc
  exact e10_endgame dt1 dt0 dtm1 g k hnueva hdtm1 hdt1 hdt0 hg_deg hg_ne0 hg_neg1

/-! ## §9. E17 — Corollary 5.2 (CONDITIONAL assembly).

  From Thm 5.1 (as `h51`) and the link hypothesis `link52` — the ψ sixth-power
  step (Cor 7.2 + Thm 2.6 + Def 4.3 of [GGV1]) together with the φ-shift
  (φ(x) = x + λ, φ(y) = y), the bracket [φ(P),φ(Q)] = x + λ, and the sucesores
  bounds (sucesores) — which turn a Cor-5.2-shaped counterexample into a
  Thm-5.1-shaped counterexample. All of those are carried inside `link52`;
  the assembly itself is the two-line application below. -/

theorem cor52_conditional (C52Counterexample S5Counterexample : Prop)
    (h51 : ¬ S5Counterexample)
    (link52 : C52Counterexample → S5Counterexample) :
    ¬ C52Counterexample := by
  intro h
  exact h51 (link52 h)
#print axioms C_mul_ofNat'
#print axioms ofNat_mul_C'
#print axioms C_mul_natCast'
#print axioms natCast_mul_C'
#print axioms C_mul_X_pow_mul_C
#print axioms X_pow_mul_C_mul_C
#print axioms C_mul_C_mul_X_pow
#print axioms C_mul_X_pow
#print axioms C_mul_X_pow_C
#print axioms e13_C3_deriv
#print axioms e13_ode
#print axioms e13_f_factor
#print axioms e13_C3_mul_f
#print axioms e13_f_natDegree
#print axioms e13_g_natDegree
#print axioms e13_g_ne_zero_at_zero
#print axioms e13_g_ne_zero_at_neg_one
#print axioms e13_bezout
#print axioms e13_f_separable
#print axioms e16_cert
#print axioms e16_principal
#print axioms e14_d_mem
#print axioms pow_ne_zero_of_ne
#print axioms val_pow
#print axioms e15_arith_neg13
#print axioms e15_arith_17
#print axioms e15_bound_neg13
#print axioms e15_bound_17
#print axioms e12_Qtilde
#print axioms e12_Ctilde_sq
#print axioms e12_remark_conditional
#print axioms e11_recursion_step
#print axioms e11_recursion_sign_slip
#print axioms e10_clearing
#print axioms e10_rescaling
#print axioms e10_dt_bound
#print axioms e10_endgame
#print axioms thm51_conditional
#print axioms cor52_conditional
