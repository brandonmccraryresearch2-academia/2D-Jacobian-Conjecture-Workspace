import Mathlib

/-! # R12 — Remark "a remark"'s two face laws + alineados(2a) (Phase 4, Leg E)

**CLAIM:** alineados(2a) is kernel from (2b); Remark "a remark"'s
consequences (1)(2)(3) are kernel conditional on the power-law premises;
the power law itself is kernel only for monomial faces.
**STATUS:**
  - KERNEL: `alineados_2a_from_2b` — Prop "P y Q alineados"(2a)
    (TeX 532: `P^n = α Q^m`) from (2b) (TeX 537–539:
    `P = λ_P R^m`, `Q = λ_Q R^n`), with `α = λ_P^n / λ_Q^m`, in any
    field. (2b) itself is CARRIED (external — it is the content of
    alineados(2) that the D2 combine leg carries as `h2a`).
  - KERNEL (conditional): `remark_ratio`, `remark_st_scaling`,
    `remark_en_scaling` — Remark "a remark" (TeX 1197–1234)
    consequences (1) `n/m = v(Q)/v(P)`, (2) `st(Q) = (n/m)·st(P)`,
    (3) `en(Q) = (n/m)·en(P)`, from the power-law premises
    `v(P) = m·v(R)`, `v(Q) = n·v(R)` and `st(P) = m•st(R)`,
    `st(Q) = n•st(R)` (and the `en` analogues). The D2 combine leg
    proved Remark "a remark" conditional on exactly these two carried
    face laws (`hpowface`: st/en of `ppow R k` have exponents `k·st/en`
    of `R`; `hface_pEq`/`hpscale`: `pEq` and nonzero scaling preserve
    st/en) — this file proves the *consequences* from the laws, so the
    remaining gap is precisely the laws themselves.
  - KERNEL: `tpow_exp`, `tpow_coeff`, `tpow_exp_smul` — the power law
    for MONOMIAL faces: the `k`-th power of a single term has exponent
    `k•e` and coefficient `c^k`. The general (non-monomial) face law
    `hpowface` is NOT proved here: for a face with several terms, the
    power's support is the `k`-fold Minkowski sum and coefficients can
    cancel, so the max/min endpoints need the full face machinery
    (Part17 `stFace`/`enFace` + the D2 `ppow` lemmas). That is the
    precise remaining R12 gap, stated here and not papered over.
**NOT proved here:** alineados(2b); the general `hpowface`;
`hface_pEq`/`hpscale`.
**Sources:** [GGV1] TeX 514–559 (alineados), 1197–1240 (Remark "a
remark"); d1_d2combine header (carried face laws, verbatim).
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- alineados(2a) from (2b): if `P = λ_P·R^m` and `Q = λ_Q·R^n` in a
field with `λ_Q ≠ 0`, then `P^n = (λ_P^n / λ_Q^m)·Q^m`. -/
theorem alineados_2a_from_2b {K : Type*} [Field K] {P Q R lamP lamQ : K}
    {m n : ℕ}
    (hP : P = lamP * R ^ m) (hQ : Q = lamQ * R ^ n) (hlQ : lamQ ≠ 0) :
    P ^ n = (lamP ^ n / lamQ ^ m) * Q ^ m := by
  rw [hP, hQ]
  field_simp
  ring

/-- Remark "a remark", consequence (1) (TeX 1214): `n/m = v(Q)/v(P)`,
from `v(P) = m·v(R)`, `v(Q) = n·v(R)` with `m > 0`, `v(R) ≠ 0`. -/
theorem remark_ratio {vP vQ vR : ℚ} {m n : ℕ} (hm : 0 < m) (hvR : vR ≠ 0)
    (hP : vP = m * vR) (hQ : vQ = n * vR) :
    (n : ℚ) / m = vQ / vP := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hP, hQ]
  field_simp

/-- Remark "a remark", consequence (2) (TeX 1218): `st(Q) = (n/m)·st(P)`,
from the power law `st(P) = m•st(R)`, `st(Q) = n•st(R)` with `m > 0`. -/
theorem remark_st_scaling {stP stQ stR : ℚ × ℚ} {m n : ℕ} (hm : 0 < m)
    (hP : stP = (m : ℚ) • stR) (hQ : stQ = (n : ℚ) • stR) :
    stQ = ((n : ℚ) / m) • stP := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hP, hQ, ← smul_assoc, smul_eq_mul, div_mul_cancel₀ _ hm']

/-- Remark "a remark", consequence (3) (TeX 1222): `en(Q) = (n/m)·en(P)`,
same proof as (2). -/
theorem remark_en_scaling {enP enQ enR : ℚ × ℚ} {m n : ℕ} (hm : 0 < m)
    (hP : enP = (m : ℚ) • enR) (hQ : enQ = (n : ℚ) • enR) :
    enQ = ((n : ℚ) / m) • enP := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hP, hQ, ← smul_assoc, smul_eq_mul, div_mul_cancel₀ _ hm']

/-- A term: exponent paired with an integer coefficient (Phase 1 `Term`). -/
abbrev Term := (Int × Int) × Int

/-- The `k`-th power of a single term: exponent scaled by `k`,
coefficient raised to `k`. (The monomial case of `ppow`.) -/
def tpow (t : Term) (k : ℕ) : Term :=
  (((k : ℤ) * t.1.1, (k : ℤ) * t.1.2), t.2 ^ k)

/-- The exponent of `t^k` is `k` times the exponent of `t`. -/
theorem tpow_exp (t : Term) (k : ℕ) :
    (tpow t k).1 = ((k : ℤ) * t.1.1, (k : ℤ) * t.1.2) :=
  rfl

/-- The coefficient of `t^k` is the `k`-th power of the coefficient. -/
theorem tpow_coeff (t : Term) (k : ℕ) : (tpow t k).2 = t.2 ^ k :=
  rfl

/-- The monomial face law: the exponent of `t^k` is `k •` the exponent
of `t` (pointwise scalar multiplication on `ℤ × ℤ`). -/
theorem tpow_exp_smul (t : Term) (k : ℕ) :
    (tpow t k).1 = (k : ℤ) • t.1 :=
  rfl
