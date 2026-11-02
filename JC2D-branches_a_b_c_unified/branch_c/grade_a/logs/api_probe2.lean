import Mathlib

-- core Nat division lemmas: check names/signatures by using them
example (x n : Nat) (h : x >>> n = 0) : x < 2 ^ n := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff.mp h).resolve_right (by simp)
example (Q D : Nat) (hD : 0 < D) (h : Q < 2 ^ 22 * D) : Q / D < 2 ^ 22 := by
  exact (Nat.div_lt_iff_lt_mul hD).mpr h
example (Q a b : Nat) (h : a ≤ b) : Q / b ≤ Q / a := Nat.div_le_div_right h
example (i : Nat) (hi : 3199 ≤ i) : (2 ^ 40) ^ 3199 ≤ (2 ^ 40) ^ i :=
  Nat.pow_le_pow_right (by decide) hi
example (a b c : Nat) (h : a < b) (hc : 0 < c) : c * a < c * b :=
  Nat.mul_lt_mul_of_pos_left h hc
example (a b c : Nat) (h : a < b) (hc : 0 < c) : a * c < b * c :=
  Nat.mul_lt_mul_of_pos_right h hc
example (l : List Nat) (f g : Nat → Nat) : (l.map g).map f = l.map (f ∘ g) :=
  List.map_map f g l
example (s : Finset (Fin 5)) (a : Fin 5) (b : Fin 5 → Nat) :
    (∑ x ∈ s, (if a = x then b x else 0)) = if a ∈ s then b a else 0 :=
  Finset.sum_ite_eq s a b
example (M N : Matrix (Fin 3) (Fin 3) (ZMod 7)) (h : ∀ i j, M i j = N i j) : M = N :=
  Matrix.ext h
example (k j : Fin 3) : (Matrix.mul_apply (1 : Matrix (Fin 3) (Fin 3) (ZMod 7)) (1 : Matrix (Fin 3) (Fin 3) (ZMod 7)) k j) = ∑ i, (1 : Matrix (Fin 3) (Fin 3) (ZMod 7)) k i * (1 : Matrix (Fin 3) (Fin 3) (ZMod 7)) i j := rfl
example (k j : Fin 3) : (1 : Matrix (Fin 3) (Fin 3) (ZMod 7)) k j = if k = j then 1 else 0 :=
  Matrix.one_apply k j
example (a b : Nat) : ((a : ZMod 32003) = (b : ZMod 32003)) ↔ a ≡ b [MOD 32003] :=
  ZMod.natCast_eq_natCast_iff a b 32003
example (a b : Fin 9) : (a = b ↔ a.val = b.val) := Fin.ext_iff
example : ∀ j : Fin 5, j.val < 7 := by decide +kernel
