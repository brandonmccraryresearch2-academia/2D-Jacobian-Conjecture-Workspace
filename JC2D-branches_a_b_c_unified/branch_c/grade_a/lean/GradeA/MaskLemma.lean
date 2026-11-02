/-!
# Branch (c) A1: the mask lemma

Standalone, core-Lean only (no Mathlib import, so it compiles in seconds).

Parameters from `branch_c/rank_lemma_check/gen_lean.py`: slot width `S_ = 40`,
`C` slots below `2 ^ 15`, `Q` slots below `2 ^ 22`, `n = 3199` columns,
`p = 32003`. The generated `RCCommon` definitions are restated here verbatim
(up to `let`-unfolding); a `rfl` bridge to the real `RCCommon` is checked
separately once the generated files exist.

Main results:
- `mask_slots`: if `x &&& maskGen W n = 0` then every slot `k < n` of `x`
  (base `2 ^ 40` digits) is below `2 ^ W`.
- `slotOK_slots`: `slotOK x = true` gives every `C` slot below `2 ^ 15`.
- `colOK_slots`: `colOK j X = true` gives every `Q` slot below `2 ^ 22`.

These discharge the `hslot` / `hQ` hypotheses of `BranchC.NoCarry.bridge`.
-/

namespace BranchC.Mask

/-- `0 < 2 ^ m`, by induction (core has no `pos_pow_of_pos` under that name). -/
theorem two_pow_pos : ∀ m : Nat, 0 < 2 ^ m
  | 0 => by decide
  | k + 1 => by rw [Nat.pow_succ]; exact Nat.mul_pos (two_pow_pos k) (by decide)

/-- Base-`B` digit: the same term as `BranchC.NoCarry.slot`. -/
def slot (B k x : Nat) : Nat := (x / B ^ k) % B

/-- Geometric factor: `∑_{k<n} 2 ^ (40 * k)`. -/
def geom (n : Nat) : Nat := (2 ^ (40 * n) - 1) / (2 ^ 40 - 1)

/-- Mask with `1` bits exactly in positions `[40 * k + W, 40 * (k + 1))`, `k < n`. -/
def maskGen (W n : Nat) : Nat := (2 ^ 40 - 2 ^ W) * geom n

/-- `(2 ^ 40 - 1)` divides `2 ^ (40 * n) - 1`. -/
theorem dvd_geom : ∀ n : Nat, (2 ^ 40 - 1) ∣ (2 ^ (40 * n) - 1)
  | 0 => ⟨0, by simp⟩
  | n + 1 => by
    have e : 2 ^ (40 * (n + 1)) - 1
        = (2 ^ (40 * n) - 1) + 2 ^ (40 * n) * (2 ^ 40 - 1) := by
      have hnk : 40 * (n + 1) = 40 * n + 40 := by omega
      rw [hnk, Nat.pow_add, Nat.mul_sub_left_distrib, Nat.mul_one]
      have hA := two_pow_pos (40 * n)
      have hle : 2 ^ (40 * n) ≤ 2 ^ (40 * n) * 2 ^ 40 := by
        have h1 : 2 ^ (40 * n) * 1 ≤ 2 ^ (40 * n) * 2 ^ 40 :=
          Nat.mul_le_mul (Nat.le_refl _) (by have := two_pow_pos 40; omega)
        rwa [Nat.mul_one] at h1
      omega
    rw [e]
    exact Nat.dvd_add (dvd_geom n) (Nat.dvd_mul_left _ _)

/-- The defining division, multiplied back out. -/
theorem geom_mul (n : Nat) : (2 ^ 40 - 1) * geom n = 2 ^ (40 * n) - 1 :=
  Nat.mul_div_cancel' (dvd_geom n)

/-- Geometric-sum step. -/
theorem geom_succ (n : Nat) : geom (n + 1) = geom n + 2 ^ (40 * n) := by
  unfold geom
  have e : 2 ^ (40 * (n + 1)) - 1
      = (2 ^ (40 * n) - 1) + 2 ^ (40 * n) * (2 ^ 40 - 1) := by
    have hnk : 40 * (n + 1) = 40 * n + 40 := by omega
    rw [hnk, Nat.pow_add, Nat.mul_sub_left_distrib, Nat.mul_one]
    have hA := two_pow_pos (40 * n)
    have hle : 2 ^ (40 * n) ≤ 2 ^ (40 * n) * 2 ^ 40 := by
      have h1 : 2 ^ (40 * n) * 1 ≤ 2 ^ (40 * n) * 2 ^ 40 :=
        Nat.mul_le_mul (Nat.le_refl _) (by have := two_pow_pos 40; omega)
      rwa [Nat.mul_one] at h1
    omega
  rw [e, Nat.mul_comm (2 ^ (40 * n)) (2 ^ 40 - 1),
    Nat.add_mul_div_left _ _ (by have := two_pow_pos 40; omega : 0 < 2 ^ 40 - 1)]

/-- Mask step: one more slot appended on top. -/
theorem maskGen_succ (W n : Nat) :
    maskGen W (n + 1) = maskGen W n + 2 ^ (40 * n) * (2 ^ 40 - 2 ^ W) := by
  unfold maskGen
  rw [geom_succ, Nat.mul_add, Nat.mul_comm (2 ^ 40 - 2 ^ W) (2 ^ (40 * n))]

/-- A mask's bits all lie below `40 * n`. -/
theorem maskGen_lt {W n : Nat} (_hW : W ≤ 40) : maskGen W n < 2 ^ (40 * n) := by
  have hle : (2 ^ 40 - 2 ^ W) * geom n ≤ (2 ^ 40 - 1) * geom n := by
    apply Nat.mul_le_mul _ (Nat.le_refl _)
    have h2W := two_pow_pos W
    omega
  calc maskGen W n ≤ (2 ^ 40 - 1) * geom n := hle
    _ = 2 ^ (40 * n) - 1 := geom_mul n
    _ < 2 ^ (40 * n) := by have := two_pow_pos (40 * n); omega

/-- Bitwise `&&&` is commutative (core has no `Nat.land_comm` under that name). -/
theorem land_comm' (a b : Nat) : a &&& b = b &&& a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

/-- Bitwise `&&&` is associative (core has no `Nat.land_assoc` under that name). -/
theorem land_assoc' (a b c : Nat) : (a &&& b) &&& c = a &&& (b &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
    Bool.and_assoc]

/-- Masking can only clear bits, so it stays below the same power of two. -/
theorem land_lt {m a c : Nat} (ha : a < 2 ^ m) : a &&& c < 2 ^ m := by
  have h1 : (a &&& c) &&& (2 ^ m - 1) = a &&& c := by
    rw [land_assoc', land_comm' c (2 ^ m - 1), ← land_assoc',
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]
  have h2 : (a &&& c) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (two_pow_pos m)
  rw [← Nat.and_two_pow_sub_one_eq_mod] at h2
  rw [h1] at h2
  exact h2

/-- Bits of a split number: low part below `m`, high part above. -/
theorem add_pow_mul_testBit {m a b i : Nat} (ha : a < 2 ^ m) :
    (a + 2 ^ m * b).testBit i
      = if i < m then a.testBit i else b.testBit (i - m) := by
  by_cases hi : i < m
  · rw [if_pos hi]
    have hmod : (a + 2 ^ m * b) % 2 ^ m = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have h1 := Nat.testBit_mod_two_pow (a + 2 ^ m * b) m i
    rw [hmod] at h1
    rw [h1]
    simp [hi]
  · rw [if_neg hi]
    have hge : m ≤ i := Nat.not_lt.mp hi
    have hshr : (a + 2 ^ m * b) >>> m = b := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (two_pow_pos m),
        Nat.div_eq_of_lt ha, Nat.zero_add]
    have h2 := Nat.testBit_shiftRight (a + 2 ^ m * b) (i := m) (j := i - m)
    rw [hshr] at h2
    have hmi : m + (i - m) = i := by omega
    rw [hmi] at h2
    exact h2.symm

/-- `&&&` splits across a low/high decomposition. -/
theorem land_split {m a b c d : Nat} (ha : a < 2 ^ m) (hc : c < 2 ^ m) :
    (a + 2 ^ m * b) &&& (c + 2 ^ m * d)
      = (a &&& c) + 2 ^ m * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, add_pow_mul_testBit ha, add_pow_mul_testBit hc,
    add_pow_mul_testBit (land_lt ha), Nat.testBit_and, Nat.testBit_and]
  by_cases hi : i < m
  · rw [if_pos hi, if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, if_neg hi]

/-- One slot: if masking with `2 ^ 40 - 2 ^ W` kills a number, its low
`2 ^ 40` part is below `2 ^ W`. -/
theorem slot_of_land {W y : Nat} (hW : W ≤ 40)
    (h : y &&& (2 ^ 40 - 2 ^ W) = 0) :
    y % 2 ^ 40 < 2 ^ W := by
  -- Bits of the single-slot mask: exactly `[W, 40)`.
  have hB : ∀ i : Nat, (2 ^ 40 - 2 ^ W).testBit i = decide (W ≤ i ∧ i < 40) := by
    intro i
    have e : 2 ^ 40 - 2 ^ W = (2 ^ (40 - W) - 1) <<< W := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm (2 ^ (40 - W) - 1) (2 ^ W),
        Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add]
      have h1 : W + (40 - W) = 40 := by omega
      rw [h1]
    rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hi1 : W ≤ i
    · have hi2 : i - W < 40 - W ↔ i < 40 := by omega
      simp [hi1, hi2]
    · simp [hi1]
  -- The masked low part is still killed.
  have hz : (y % 2 ^ 40) &&& (2 ^ 40 - 2 ^ W) = 0 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod, land_assoc',
      land_comm' (2 ^ 40 - 1) (2 ^ 40 - 2 ^ W), ← land_assoc', h]
    rfl
  -- Hence the high part of the low part vanishes.
  have hdiv : (y % 2 ^ 40) / 2 ^ W = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    have hsh : ((y % 2 ^ 40) / 2 ^ W).testBit j
        = (y % 2 ^ 40).testBit (W + j) := by
      rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    rw [hsh, Nat.testBit_mod_two_pow]
    have h0 : (0 : Nat).testBit j = false := Nat.zero_testBit j
    rw [h0]
    by_cases hj : W + j < 40
    · have hbT : (2 ^ 40 - 2 ^ W).testBit (W + j) = true := by
        rw [hB]
        simp [hj, Nat.le_add_right]
      have hzT := congrArg (fun t => t.testBit (W + j)) hz
      have h0W : (0 : Nat).testBit (W + j) = false := Nat.zero_testBit _
      rw [Nat.testBit_and, hbT, Bool.and_true, h0W] at hzT
      rw [Nat.testBit_mod_two_pow] at hzT
      simp [hj] at hzT
      simp [hj, hzT]
    · simp [hj]
  have hdecomp := Nat.div_add_mod (y % 2 ^ 40) (2 ^ W)
  rw [hdiv, Nat.mul_zero, Nat.zero_add] at hdecomp
  rw [← hdecomp]
  exact Nat.mod_lt _ (two_pow_pos W)

/-- The mask lemma: masked numbers have small slots. -/
theorem mask_slots {W : Nat} (hW : W ≤ 40) :
    ∀ (n : Nat) {x : Nat},
      x &&& maskGen W n = 0 → ∀ k, k < n → slot (2 ^ 40) k x < 2 ^ W := by
  intro n
  induction n with
  | zero => intro x _ k hk; omega
  | succ n ih =>
    intro x h k hk
    rw [maskGen_succ] at h
    generalize hx_lo : x % 2 ^ (40 * n) = x_lo
    generalize hx_hi : x / 2 ^ (40 * n) = x_hi
    have hx : x = x_lo + 2 ^ (40 * n) * x_hi := by
      rw [← hx_lo, ← hx_hi]
      have hdm := Nat.div_add_mod x (2 ^ (40 * n))
      omega
    have hlo_lt : x_lo < 2 ^ (40 * n) := by
      rw [← hx_lo]
      exact Nat.mod_lt _ (two_pow_pos _)
    have hsplit := land_split (m := 40 * n) (a := x_lo) (b := x_hi)
      (c := maskGen W n) (d := 2 ^ 40 - 2 ^ W)
      hlo_lt (maskGen_lt hW)
    rw [← hx] at hsplit
    rw [h] at hsplit
    have hsum : (x_lo &&& maskGen W n) + 2 ^ (40 * n) * (x_hi &&& (2 ^ 40 - 2 ^ W))
        = 0 := hsplit.symm
    have ⟨hlo, hhi'⟩ := Nat.add_eq_zero_iff.mp hsum
    have hhi : x_hi &&& (2 ^ 40 - 2 ^ W) = 0 :=
      (Nat.mul_eq_zero.mp hhi').elim
        (fun h0 => by have hp := two_pow_pos (40 * n); omega)
        (fun h0 => h0)
    by_cases hkn : k < n
    · have hslot : slot (2 ^ 40) k x = slot (2 ^ 40) k x_lo := by
        unfold slot
        rw [← Nat.pow_mul]
        have h1 : x / 2 ^ (40 * k)
            = x_lo / 2 ^ (40 * k) + 2 ^ (40 * (n - k)) * x_hi := by
          rw [hx]
          have hnk : 40 * n = 40 * k + 40 * (n - k) := by omega
          rw [hnk, Nat.pow_add, Nat.mul_assoc,
            Nat.add_mul_div_left _ _ (two_pow_pos _)]
        rw [h1]
        have hnk1 : 40 * (n - k) = 40 + 40 * (n - k - 1) := by omega
        rw [hnk1, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      rw [hslot]
      exact ih hlo k hkn
    · have hkn2 : k = n := by omega
      rw [hkn2]
      have h2 : x / 2 ^ (40 * n) = x_hi := by
        rw [hx, Nat.add_mul_div_left _ _ (two_pow_pos _), ← hx_lo,
          Nat.div_eq_of_lt (Nat.mod_lt _ (two_pow_pos _)), Nat.zero_add]
      unfold slot
      rw [← Nat.pow_mul, h2]
      exact slot_of_land hW hhi

/-- The generated `RCCommon` masks, restated verbatim (up to `let`-unfolding). -/
def maskC : Nat := maskGen 15 3199
def maskQ : Nat := maskGen 22 3199

/-- The generated `RCCommon.slotOK`, restated verbatim. -/
def slotOK (x : Nat) : Bool := (x &&& maskC == 0) && (x >>> (40 * 3199) == 0)

/-- The generated `RCCommon.colOK`, restated verbatim (`let`-unfolded). -/
def colOK (j X : Nat) : Bool :=
  (32003 * ((X - 2 ^ (40 * j)) / 32003) + 2 ^ (40 * j) == X) &&
  (((X - 2 ^ (40 * j)) / 32003) &&& maskQ == 0)

/-- `slotOK` gives every `C` slot below `2 ^ 15`. -/
theorem slotOK_slots {x : Nat} (h : slotOK x = true) :
    ∀ k, k < 3199 → slot (2 ^ 40) k x < 2 ^ 15 := by
  have h1 : (x &&& maskC == 0) = true := by
    unfold slotOK at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have h2 : x &&& maskC = 0 := beq_iff_eq.mp h1
  exact mask_slots (W := 15) (by decide : 15 ≤ 40) (n := 3199) h2

/-- `colOK` gives every `Q` slot below `2 ^ 22`. -/
theorem colOK_slots {j X : Nat} (h : colOK j X = true) :
    ∀ k, k < 3199 → slot (2 ^ 40) k ((X - 2 ^ (40 * j)) / 32003) < 2 ^ 22 := by
  have h1 : (((X - 2 ^ (40 * j)) / 32003) &&& maskQ == 0) = true := by
    unfold colOK at h
    rw [Bool.and_eq_true] at h
    exact h.2
  have h2 : ((X - 2 ^ (40 * j)) / 32003) &&& maskQ = 0 := beq_iff_eq.mp h1
  exact mask_slots (W := 22) (by decide : 22 ≤ 40) (n := 3199) h2

end BranchC.Mask
