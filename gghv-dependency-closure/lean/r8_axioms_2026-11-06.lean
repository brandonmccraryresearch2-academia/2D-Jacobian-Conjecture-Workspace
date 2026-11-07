import Mathlib

/-! # R8 — Esquina (3) ℓ-form (Phase 4, Leg E)

**CLAIM:** Kernel arithmetic for the esquina(3) ℓ-form tail + a conditional
ℓ-form assembly theorem.
**STATUS:** Direction half already kernel in `d1_esquina3_2026-11-05.lean`
(`esquina_item3_dir`, `esquina_item3_dir_cases`, permitted triple). This file
adds, all kernel unless marked CONDITIONAL:
  (a) the valuation `v_{-1,3}(8,3) = 1` and `m + n - 2 > 0`;
  (b) the three `b'`-case direction determinations, assembled into
      `esq3_dir_determination` (the `a' = -2, -3` discards and the central(4)
      exclusion of `(1,1)` are explicit hypotheses — they are the two steps
      of the paper's argument that cite central, not proved here);
  (c) the two φ-argument impossibilities (aligned case: no integers satisfy
      `3b''-a'' < 1 ∧ 2b''-a'' > 0`; non-aligned case: no `k ≥ 1` with
      `k+1 < 2`);
  (d) the ℓ-form support/valuation facts: every term of
      `x^{-m}(x³y-μ)^{3m}` has `(-1,3)`-valuation `m`, endpoints `(-m,0)`
      and `(8m,3m)`;
  (e) CONDITIONAL `esq3_lform_from_cube`: from the common-power premise
      `ℓ(P) = λ_P R^m` (Remark "a remark", TeX 1197 — itself conditional on
      alineados(2a) + face laws, see R12) and the cube premise
      `x·R = c·(z-μ)³` (the "𝔯 has no simple linear factor" step, which
      needs the φ-argument re-application of (1)/(2) — carried here as the
      cube hypothesis, not proved), the multiplied ℓ-form
      `x^m·ℓ(P) = (λ_P·c^m)·(z-μ)^{3m}` follows by a ring identity.
      The same theorem with `m := n` gives the Q-form.
**NOT proved here:** the cube premise itself (φ-argument); the common-power
premise (R12 conditional); the identification of `ℓ_{-1,3}(P)` with the
face polynomial in the KTerm list model (needs the D2 bridge — the
`esq3_lform_from_cube` statement is in an abstract commutative ring, so
the bridge to `MvPolynomial`/KTerm lists is still open).
**Sources:** [GGV1] TeX 5468–5585 (esquina(3) proof); inventory.md
"esquina(3) tail READ" entry. No `sorry` anywhere; no `axiom` anywhere.
-/

/-- Weighted valuation (Part14, verbatim from the Phase 1 files). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Cross product of two integer vectors. -/
def crossProd (a b : Int × Int) : Int := a.1 * b.2 - a.2 * b.1

/-- Primitive direction of a vector: `dir(v) = (-b/g, a/g)`, `g = gcd(a,b)`. -/
def dirOf (v : Int × Int) : Int × Int :=
  (-v.2 / (Int.gcd v.1 v.2 : Int), v.1 / (Int.gcd v.1 v.2 : Int))

/-- `v_{-1,3}(8,3) = 1` (TeX 5530: `v_{-1,3}(P) = m·v_{-1,3}(8,3) = m`). -/
theorem esq3_val_8_3 : dirVal (-1) 3 8 3 = 1 := by decide

/-- `m + n - 2 > 0` from `m, n ≥ 1`, `m ≠ n` (TeX 5532–5534). -/
theorem esq3_mn_sum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    2 < m + n := by omega

/-- `b' ∈ {0,1,2}` from `0 ≤ b' < 3` (TeX 5474–5478: `b' < v_{01}(a,b) = 3`). -/
theorem esq3_b'_cases {b' : ℤ} (hb0 : 0 ≤ b') (hb3 : b' < 3) :
    b' = 0 ∨ b' = 1 ∨ b' = 2 := by omega

/-- The three direction determinations (TeX 5491–5498):
`dir((8,3)-(5,2)) = dir(3,1) = (-1,3)`, `dir((8,3)-(2,1)) = dir(6,2)`,
`dir((8,3)-(-1,0)) = dir(9,3)`. -/
theorem esq3_dir_b2 : dirOf ((8, 3) - (5, 2) : Int × Int) = (-1, 3) := by decide
theorem esq3_dir_b1 : dirOf ((8, 3) - (2, 1) : Int × Int) = (-1, 3) := by decide
theorem esq3_dir_b0 : dirOf ((8, 3) - (-1, 0) : Int × Int) = (-1, 3) := by decide

/-- Full direction determination (TeX 5481–5519): from the caso-alineado
inequalities `8b'-3a' > 0`, `4 > 4b'-a'`, `b' ∈ {0,1,2}`, the central(4)
exclusion of `(a',b') = (1,1)` (`h11`), and the discards of `a' = -2, -3`
at `b' = 0` (`hdisc`, which cite central(2)(3) + F-no-es-monomio in the
paper and are carried here as hypotheses), `(ρ₂,σ₂) = (-1,3)`. -/
theorem esq3_dir_determination {a' b' : ℤ} (hb0 : 0 ≤ b') (hb3 : b' < 3)
    (h1 : 0 < 8 * b' - 3 * a') (h2 : 4 * b' - a' < 4)
    (h11 : ¬ (a' = 1 ∧ b' = 1))
    (hdisc : b' = 0 → a' ≠ -2 ∧ a' ≠ -3) :
    dirOf (8 - a', 3 - b') = (-1, 3) := by
  rcases esq3_b'_cases hb0 hb3 with hb | hb | hb
  · subst hb
    have ha : a' = -1 := by
      have h := hdisc rfl
      omega
    subst ha
    exact esq3_dir_b0
  · subst hb
    have ha : a' = 2 := by omega
    subst ha
    exact esq3_dir_b1
  · subst hb
    have ha : a' = 5 := by omega
    subst ha
    exact esq3_dir_b2

/-- φ-argument, aligned case (TeX 5571–5576): the inequalities
`3b''-a'' < 1` and `2b''-a'' > 0` are jointly impossible for integers
(`b'' ≥ 0` is `(a'',b'') ∈ ℤ × ℕ₀` from (1)). -/
theorem esq3_phi_aligned_impossible {a'' b'' : ℤ} (hb : 0 ≤ b'')
    (h1 : 3 * b'' - a'' < 1) (h2 : 0 < 2 * b'' - a'') : False := by omega

/-- φ-argument, non-aligned case (TeX 5577–5583): no `k ∈ ℕ`, `k ≥ 1`,
satisfies `k + 1 < 2`. -/
theorem esq3_phi_nonaligned_impossible {k : ℕ} (hk : 1 ≤ k) (h : k + 1 < 2) :
    False := by omega

/-- Every term of the ℓ-form has `(-1,3)`-valuation `m`: the `j`-th term of
`x^{-m}(x³y-μ)^{3m}` sits at `(-m + 3j, j)`. -/
theorem esq3_lform_term_val {m j : ℤ} :
    dirVal (-1) 3 (-m + 3 * j) j = m := by
  simp [dirVal]

/-- The `j = 0` endpoint of the ℓ-form support is `(-m, 0)`. -/
theorem esq3_lform_endpoint_lo {m : ℤ} :
    (-m + 3 * (0 : ℤ), (0 : ℤ)) = (-m, 0) := by simp

/-- The `j = 3m` endpoint of the ℓ-form support is `(8m, 3m)`. -/
theorem esq3_lform_endpoint_hi {m : ℤ} :
    (-m + 3 * (3 * m), 3 * m) = (8 * m, 3 * m) := by
  ext <;> simp <;> ring

/-- CONDITIONAL ℓ-form assembly (TeX 5536–5547): from the common-power form
`ℓ(P) = λ_P R^m` and the cube form `x·R = c·(z-μ)³` (with `z = x³y`),
the multiplied ℓ-form `x^m·ℓ(P) = (λ_P·c^m)·(z-μ)^{3m}`.
The `x^{-m}` in the paper's statement is the multiplied-out form. -/
theorem esq3_lform_from_cube {K : Type*} [Field K] {x z R lP : K}
    {lamP c mu : K} {m : ℕ}
    (hcommon : lP = lamP * R ^ m)
    (hxcube : x * R = c * (z - mu) ^ 3) :
    x ^ m * lP = (lamP * c ^ m) * (z - mu) ^ (3 * m) := by
  calc x ^ m * lP = lamP * (x ^ m * R ^ m) := by rw [hcommon]; ring
    _ = lamP * (x * R) ^ m := by rw [mul_pow]
    _ = lamP * (c * (z - mu) ^ 3) ^ m := by rw [hxcube]
    _ = (lamP * c ^ m) * (z - mu) ^ (3 * m) := by
        rw [mul_pow, ← pow_mul]; ring

/-- The Q-form is the same theorem with `m := n` (TeX 5525–5527). -/
theorem esq3_lform_Q {K : Type*} [Field K] {x z RQ lQ : K}
    {lamQ c mu : K} {n : ℕ}
    (hcommon : lQ = lamQ * RQ ^ n)
    (hxcube : x * RQ = c * (z - mu) ^ 3) :
    x ^ n * lQ = (lamQ * c ^ n) * (z - mu) ^ (3 * n) :=
  esq3_lform_from_cube hcommon hxcube

#print axioms esq3_dir_b2
#print axioms esq3_dir_b1
#print axioms esq3_dir_b0
#print axioms esq3_lform_endpoint_lo
#print axioms esq3_lform_endpoint_hi
#print axioms esq3_lform_Q
