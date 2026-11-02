/- NoCarryBridge — the no-carry digit argument for A1.

    The packed kernel check (`rank_lemma_check/gen_lean.py`)
    proves, for every pivot column j, `colOK j X = true` where
    X = Σₜ vₜ · Cpk_{iₜ}, and `slotOK Cpk_i = true` for every
    column i of C. This file proves the digit side of the
    implication those identities carry:

    - `slot B k x := (x / B^k) % B` is the k-th base-B digit.
    - `slot_add`: digits add without carry when the digitwise
      sums stay below B.
    - `slot_sum`: the same for a list of terms.
    - `colOK` digit equation: from `p * Q + E = X` (E =
      B^j) and digit bounds on Q, `slot k X = p * slot k Q
      + δ_{kj}`.
    - The bridge theorem: from the term sum, the colOK
      identity, and digit bounds on the C columns and on Q,
      `Σₜ vₜ * slot k (Cpk_{iₜ}) ≡ δ_{kj} [MOD p]` for every
      k — i.e. `(C · M_S)[k, j] ≡ δ_{kj}` in entry-sum form.

    What is NOT in this file (the remaining A1 step, next
    session): the mask lemma — `slotOK x = true` implies
    `slot k x < 2^15` for k < 3199, and `colOK j X = true`
    implies `slot k Q < 2^22` for the Q it defines. Those two
    bounds appear below as hypotheses `hslot` and `hQ`;
    nothing here claims them. The matrix-product step
    (entry sum = `Matrix.mul` entry, via the sparsity of
    M_S) is part of A1's instantiation, not of this bridge.

    Parameters (from `gen_lean.py`): p = 32003, B = 2^40,
    C slots < 2^15, Q slots < 2^22, at most 52 terms per
    column, coefficients < p. The lemmas below are stated
    for general B, p, with the numeric bounds discharged
    by `decide` at the concrete values.

    No `sorry`, no `axiom`, no `native_decide`. -/

import Mathlib

namespace BranchC.NoCarry

/-- The k-th base-B digit of x. -/
def slot (B k x : Nat) : Nat := (x / B ^ k) % B

theorem slot_zero (B x : Nat) : slot B 0 x = x % B := by
  simp [slot]

/-- Division of a sum by B, when the remainders do not carry. -/
theorem div_add_of_slot_lt {B a b : Nat} (_hB : 0 < B)
    (h : a % B + b % B < B) : (a + b) / B = a / B + b / B := by
  have ha := Nat.div_add_mod a B
  have hb := Nat.div_add_mod b B
  have h1 : B * (a / B + b / B) = B * (a / B) + B * (b / B) := by
    rw [mul_add]
  have hsum : a + b = B * (a / B + b / B) + (a % B + b % B) := by omega
  have hprod : (a / B + b / B + 1) * B = B * (a / B + b / B) + B := by ring
  have hcomm : (a / B + b / B) * B = B * (a / B + b / B) := Nat.mul_comm _ _
  rw [hsum]
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

/-- Digits add without carry. -/
theorem slot_add {B : Nat} (hB : 0 < B) : ∀ (a b k : Nat),
    (∀ j, j ≤ k → slot B j a + slot B j b < B) →
      slot B k (a + b) = slot B k a + slot B k b := by
  intro a b k
  induction k generalizing a b with
  | zero =>
    intro h
    have h0 := h 0 (Nat.le_refl 0)
    simp only [slot, pow_zero, Nat.div_one] at h0
    simp only [slot, pow_zero, Nat.div_one]
    rw [Nat.add_mod]
    exact Nat.mod_eq_of_lt h0
  | succ k ih =>
    intro h
    have hdiv : ∀ x : Nat, slot B (k + 1) x = slot B k (x / B) := by
      intro x
      simp only [slot, pow_succ, mul_comm (B ^ k) B, ← Nat.div_div_eq_div_mul]
    have e : ∀ x : Nat, ∀ j : Nat, slot B j (x / B) = slot B (j + 1) x := by
      intro x j
      simp only [slot, pow_succ]
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm B (B ^ j)]
    rw [hdiv, hdiv, hdiv,
      div_add_of_slot_lt hB (by
        have h0 := h 0 (Nat.zero_le _)
        simpa [slot] using h0)]
    apply ih
    intro j hj
    rw [e, e]
    exact h (j + 1) (Nat.succ_le_succ hj)

/-- Digits of a list sum, without carry. -/
theorem slot_sum {B : Nat} (hB : 0 < B) :
    ∀ (l : List Nat) (k : Nat),
      (∀ j, j ≤ k → (l.map (slot B j)).sum < B) →
      slot B k l.sum = (l.map (slot B k)).sum := by
  intro l
  induction l with
  | nil =>
    intro k _
    simp [slot]
  | cons a l ih =>
    intro k h
    simp only [List.map_cons, List.sum_cons]
    have htail : ∀ j, j ≤ k → (l.map (slot B j)).sum < B := by
      intro j hj
      have hj2 := h j hj
      simp only [List.map_cons, List.sum_cons] at hj2
      omega
    rw [slot_add hB a l.sum k (fun j hj => by
      rw [ih j (fun j' hj' => htail j' (Nat.le_trans hj' hj))]
      have hj2 := h j hj
      simp only [List.map_cons, List.sum_cons] at hj2
      exact hj2)]
    rw [ih k htail]

/-- Digits of a scalar multiple, without carry. -/
theorem slot_nsmul {B : Nat} (hB : 0 < B) (v x k : Nat)
    (h : ∀ j, j ≤ k → v * slot B j x < B) :
    slot B k (v * x) = v * slot B k x := by
  have hsum : v * x = (List.replicate v x).sum := by
    rw [List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  rw [hsum]
  rw [slot_sum hB]
  · rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  · intro j hj
    simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
    exact h j hj

/-- Digits of a base-B power: the Kronecker delta. -/
theorem slot_pow (B : Nat) (hB : 1 < B) (k j : Nat) :
    slot B k (B ^ j) = if k = j then 1 else 0 := by
  by_cases hkj : k = j
  · rw [← hkj]
    have h1 : slot B k (B ^ k) = 1 := by
      show (B ^ k / B ^ k) % B = 1
      rw [Nat.div_self (pow_pos (by omega : 0 < B) k)]
      exact Nat.mod_eq_of_lt hB
    rw [h1, if_pos rfl]
  · rw [if_neg hkj]
    by_cases hlt : k < j
    · have h1 : B ^ j / B ^ k = B ^ (j - k) := by
        have hj : j = k + (j - k) := by omega
        conv_lhs => rw [hj, pow_add]
        exact Nat.mul_div_cancel_left _ (pow_pos (by omega : 0 < B) k)
      simp only [slot]
      rw [h1]
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_pow_self B (by omega : j - k ≠ 0)
    · have hle : j < k := by omega
      have hdiv : B ^ j / B ^ k = 0 := by
        rw [Nat.div_eq_zero_iff]
        right
        exact pow_lt_pow_right₀ hB hle
      simp only [slot]
      rw [hdiv, Nat.zero_mod]

/-- The colOK digit equation, from `p * Q + B^j = X` and digit
    bounds on Q. -/
theorem slot_colOK {B p : Nat} (hB : 1 < B) (_hp : 0 < p)
    (Q X : Nat) (j k : Nat) (hX : p * Q + B ^ j = X)
    (hQ : ∀ i, p * slot B i Q + 1 < B) :
    slot B k X = p * slot B k Q + (if k = j then 1 else 0) := by
  rw [← hX]
  have hQk : ∀ i, i ≤ k → slot B i (p * Q) + slot B i (B ^ j) < B := by
    intro i _
    rw [slot_nsmul (by omega : 0 < B) p Q i (fun j' _ => by
      have := hQ j'
      omega)]
    rw [slot_pow B hB]
    by_cases hij : i = j
    · rw [if_pos hij]
      exact hQ i
    · rw [if_neg hij]
      have := hQ i
      omega
  rw [slot_add (by omega : 0 < B) (p * Q) (B ^ j) k hQk,
    slot_nsmul (by omega : 0 < B) p Q k (fun j' _ => by
      have := hQ j'
      omega),
    slot_pow B hB]

/-- Sum congruence for mapped lists, by induction (avoids
    library lemma names that shifted between versions). -/
theorem sum_map_congr {f g : Nat × Nat → Nat} : ∀ (l : List (Nat × Nat)),
    (∀ t ∈ l, f t = g t) → (l.map f).sum = (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons t ts ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    rw [h t List.mem_cons_self,
      ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

/-- The bridge: from the term sum, the colOK identity, and
    digit bounds on the terms and on Q, the entry sum is
    the Kronecker delta modulo p. Here `terms` is the list
    of (coefficient, packed column) pairs for one pivot
    column j of M_S; `t.1 * slot B k t.2` is the k-th entry
    of the product C · M_S in that column. -/
theorem bridge {B p : Nat} (hB : 1 < B) (hp : 0 < p)
    (terms : List (Nat × Nat)) (X Q : Nat) (j k : Nat)
    (hX : (terms.map (fun t => t.1 * t.2)).sum = X)
    (hcol : p * Q + B ^ j = X)
    (hterm : ∀ i, i ≤ k → (terms.map (fun t => t.1 * slot B i t.2)).sum < B)
    (hsc : ∀ t ∈ terms, ∀ i, i ≤ k → t.1 * slot B i t.2 < B)
    (hQ : ∀ i, p * slot B i Q + 1 < B) :
    (terms.map (fun t => t.1 * slot B k t.2)).sum ≡
      (if k = j then 1 else 0) [MOD p] := by
  have hslot_sum : slot B k X = (terms.map (fun t => t.1 * slot B k t.2)).sum := by
    rw [← hX]
    rw [slot_sum (by omega : 0 < B) _ k (fun i hi => by
      rw [List.map_map]
      have hEq : (terms.map (slot B i ∘ fun t => t.1 * t.2)).sum =
          (terms.map (fun t => t.1 * slot B i t.2)).sum :=
        sum_map_congr _ (fun t ht =>
          slot_nsmul (by omega : 0 < B) t.1 t.2 i
            (fun j hj => hsc t ht j (Nat.le_trans hj hi)))
      rw [hEq]
      exact hterm i hi)]
    rw [List.map_map]
    exact sum_map_congr _ (fun t ht =>
      slot_nsmul (by omega : 0 < B) t.1 t.2 k
        (fun j hj => hsc t ht j hj))
  have hcol_eq := slot_colOK hB hp Q X j k hcol hQ
  rw [hslot_sum] at hcol_eq
  rw [hcol_eq]
  have hmod : (p * slot B k Q + (if k = j then 1 else 0)) % p =
      (if k = j then 1 else 0) % p := by
    rw [Nat.add_comm (p * slot B k Q) (if k = j then 1 else 0),
      Nat.add_mul_mod_self_left]
  exact hmod

end BranchC.NoCarry

#print axioms BranchC.NoCarry.bridge
#print axioms BranchC.NoCarry.slot_colOK
#print axioms BranchC.NoCarry.slot_add
