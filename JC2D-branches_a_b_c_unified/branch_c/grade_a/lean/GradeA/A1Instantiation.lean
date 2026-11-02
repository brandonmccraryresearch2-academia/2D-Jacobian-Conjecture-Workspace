/- A1 instantiation: `Cinv * MS = 1` over `Matrix (Fin 3199) (Fin 3199) (ZMod 32003)`.

    The packed kernel check (`rank_lemma_check`) proves, for every pivot column j,
    `colOK j X = true` where X is the explicit coefficient × Cpk sum, and
    `slotOK Cpk_i = true` for every column i of C. This file turns those
    identities, via the no-carry bridge (`NoCarryBridge.lean`) and the mask
    lemma (`MaskLemma.lean`), into the matrix identity A1.

    Data (from the kept `INVERSE.pkl`, see `A1Data.lean`):
    - `colDataNat j` = colv[j], the (row, value) entries of pivot column j of M_S.
    - `CpkFunNat i` = Cpk_i, the packed column i of C.
    - `XSumNat j` = the col_j sum, in exactly the RCCheck `col_j` form.

    Proof outline:
    - Dispatch lemmas (`colThm`, `slotThm`, `hX_all`, data bounds) are proved by
      `decide +kernel` over `Fin 3199` (kernel re-check; no matcher needed).
    - `Cinv k i` is the k-th base-2^40 digit of `CpkFunNat i`; `MS i j` is the
      pivot-column-j value at row i, as a sparse list sum.
    - The full Finset product sum reduces to the sparse list sum (`entry_sparse`)
      via MS sparsity; the bridge then gives each entry ≡ δ (mod 32003), which
      is the ZMod entry equality.
-/

import Mathlib
import RCCommon
import GradeA.A1Data
import MaskLemma
import NoCarryBridge
import A1DispatchAsm
import A1DispatchHXAsm

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000

namespace BranchC.A1Inst

open BranchC.A1Data

/-- Cinv as a matrix: entry (k, i) is the k-th base-2^40 digit of Cpk_i. -/
noncomputable def Cinv : Matrix (Fin 3199) (Fin 3199) (ZMod 32003) :=
  fun k i => (BranchC.NoCarry.slot (2 ^ 40) k.val (CpkFunNat i.val) : ZMod 32003)

/-- MS as a matrix: entry (i, j) is the pivot-column-j value at row i. -/
noncomputable def MS : Matrix (Fin 3199) (Fin 3199) (ZMod 32003) :=
  fun i j => ((colDataNat j.val).map
    (fun t => if t.1 = i.val then (t.2 : ZMod 32003) else 0)).sum

/-! ### Dispatch lemmas (imported)

`termsFunNat` comes from A1DispatchBase; `colThm`, `slotThm`,
`coeff_bound`, `length_bound`, `row_bound` from A1DispatchAsm (400-column
chunks + by_cases assembly); `hX_all` from A1DispatchHXAsm (100-column
chunks + by_cases assembly). Same names and signatures as the original
dispatch section, so the rest of this file is unchanged. -/

/-! ### Digit bounds from the mask lemma -/

/-- Every base-2^40 digit of a packed C column is below 2^15. -/
theorem slot_bounds (i : Fin 3199) (k : Nat) (hk : k < 3199) :
    BranchC.NoCarry.slot (2 ^ 40) k (CpkFunNat i.val) < 2 ^ 15 := by
  have hM : BranchC.Mask.slotOK (CpkFunNat i.val) = true := slotThm i
  exact BranchC.Mask.slotOK_slots hM k hk

/-- Every packed C column is below 2^(40·3199) (the shift half of `slotOK`). -/
theorem cpk_lt (i : Fin 3199) : CpkFunNat i.val < 2 ^ (40 * 3199) := by
  have hM : BranchC.Mask.slotOK (CpkFunNat i.val) = true := slotThm i
  unfold BranchC.Mask.slotOK at hM
  rw [Bool.and_eq_true] at hM
  have hshift : (CpkFunNat i.val >>> (40 * 3199) == 0) = true := hM.2
  have h0 : CpkFunNat i.val >>> (40 * 3199) = 0 := beq_iff_eq.mp hshift
  rw [Nat.shiftRight_eq_div_pow] at h0
  have hlt : CpkFunNat i.val / 2 ^ (40 * 3199) < 1 := by rw [h0]; decide
  have hmul := (Nat.div_lt_iff_lt_mul (pow_pos (by decide : (0 : Nat) < 2) _)).mp hlt
  simpa using hmul

/-! ### List-sum helpers -/

theorem sum_le {l : List (Nat × Nat)} {f : (Nat × Nat) → Nat} {M : Nat}
    (h : ∀ t ∈ l, f t ≤ M) : (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have iht := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    have ht0 := h t List.mem_cons_self
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem map_sum_congr {β : Type*} [AddCommMonoid β] {l : List (Nat × Nat)}
    {f g : (Nat × Nat) → β}
    (h : ∀ t ∈ l, f t = g t) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h t List.mem_cons_self,
      ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

theorem mul_list_sum (a : ZMod 32003) (l : List (Nat × Nat))
    (f : (Nat × Nat) → ZMod 32003) :
    a * (l.map f).sum = (l.map (fun t => a * f t)).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem finset_sum_list_sum (s : Finset (Fin 3199)) (l : List (Nat × Nat))
    (g : (Fin 3199) → (Nat × Nat) → ZMod 32003) :
    (∑ i ∈ s, (l.map (g i)).sum) = (l.map (fun t => ∑ i ∈ s, g i t)).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-! ### The X bound, and Q's digits at every index -/

/-- The col_j sum is below 2^21 · 2^(40·3199): at most 52 terms, each below
    32002 · 2^(40·3199). -/
theorem xsum_bound (j : Fin 3199) :
    XSumNat j.val < 2 ^ 21 * 2 ^ (40 * 3199) := by
  rw [← hX_all j]
  have hle : ((termsFunNat j.val).map (fun t => t.1 * t.2)).sum
      ≤ (termsFunNat j.val).length * (32002 * (2 ^ (40 * 3199) - 1)) := by
    apply sum_le
    intro t ht
    simp only [termsFunNat, List.mem_map] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    have hv : p.2 < 32003 := coeff_bound j p hp
    have hc : CpkFunNat p.1 < 2 ^ (40 * 3199) :=
      cpk_lt ⟨p.1, row_bound j p hp⟩
    have h1 : p.2 ≤ 32002 := by omega
    have h2 : CpkFunNat p.1 ≤ 2 ^ (40 * 3199) - 1 := by omega
    exact Nat.mul_le_mul h1 h2
  have hlen : (termsFunNat j.val).length ≤ 52 := by
    simp only [termsFunNat, List.length_map]
    exact length_bound j
  calc ((termsFunNat j.val).map (fun t => t.1 * t.2)).sum
      ≤ (termsFunNat j.val).length * (32002 * (2 ^ (40 * 3199) - 1)) := hle
    _ ≤ 52 * (32002 * (2 ^ (40 * 3199) - 1)) :=
        Nat.mul_le_mul hlen (le_refl _)
    _ < 2 ^ 21 * 2 ^ (40 * 3199) := by
        have hpos : 0 < 2 ^ (40 * 3199) := pow_pos (by decide) _
        have e1 : 52 * (32002 * (2 ^ (40 * 3199) - 1))
            < 52 * (32002 * 2 ^ (40 * 3199)) := by
          apply Nat.mul_lt_mul_of_pos_left _ (by decide : 0 < 52)
          apply Nat.mul_lt_mul_of_pos_left _ (by decide : 0 < 32002)
          omega
        have e2 : 52 * (32002 * 2 ^ (40 * 3199))
            = (52 * 32002) * 2 ^ (40 * 3199) := by ring
        have e3 : (52 * 32002) * 2 ^ (40 * 3199)
            < 2 ^ 21 * 2 ^ (40 * 3199) := by
          apply Nat.mul_lt_mul_of_pos_right _ hpos
          decide
        exact lt_trans e1 (by rw [e2]; exact e3)

/-- Every base-2^40 digit of Q is below 2^22, at every index: below 3199 by
    `colOK_slots`, at and above 3199 by the X bound (Q has no digits there
    beyond a small top digit). -/
theorem q_slots_all (j : Fin 3199) :
    ∀ i, BranchC.NoCarry.slot (2 ^ 40) i
      ((XSumNat j.val - 2 ^ (40 * j.val)) / 32003) < 2 ^ 22 := by
  intro i
  by_cases hi : i < 3199
  · have hM : BranchC.Mask.colOK j.val (XSumNat j.val) = true := colThm j
    exact BranchC.Mask.colOK_slots hM i hi
  · push_neg at hi
    have hQlt : (XSumNat j.val - 2 ^ (40 * j.val)) / 32003
        < 2 ^ (40 * 3199 + 21) := by
      have h1 : (XSumNat j.val - 2 ^ (40 * j.val)) / 32003 ≤ XSumNat j.val :=
        le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
      have h2 := xsum_bound j
      have h3 : 2 ^ 21 * 2 ^ (40 * 3199) = 2 ^ (40 * 3199 + 21) :=
        calc 2 ^ 21 * 2 ^ (40 * 3199)
            = 2 ^ (21 + 40 * 3199) := (Nat.pow_add 2 21 (40 * 3199)).symm
          _ = 2 ^ (40 * 3199 + 21) := by rw [Nat.add_comm 21 (40 * 3199)]
      rw [h3] at h2
      exact lt_of_le_of_lt h1 h2
    have hle : BranchC.NoCarry.slot (2 ^ 40) i
        ((XSumNat j.val - 2 ^ (40 * j.val)) / 32003)
        ≤ (XSumNat j.val - 2 ^ (40 * j.val)) / 32003 / (2 ^ 40) ^ i := by
      unfold BranchC.NoCarry.slot
      exact Nat.mod_le _ _
    have hD : 0 < (2 ^ 40) ^ i := pow_pos (by decide) i
    have hlt : (XSumNat j.val - 2 ^ (40 * j.val)) / 32003 / (2 ^ 40) ^ i
        < 2 ^ 22 := by
      rw [Nat.div_lt_iff_lt_mul hD]
      have hpow : (2 ^ 40) ^ 3199 ≤ (2 ^ 40) ^ i :=
        Nat.pow_le_pow_right (by decide) hi
      have h22 : 2 ^ 22 * (2 ^ 40) ^ 3199 = 2 ^ (40 * 3199 + 22) :=
        calc 2 ^ 22 * (2 ^ 40) ^ 3199
            = 2 ^ 22 * 2 ^ (40 * 3199) := by rw [Nat.pow_mul]
          _ = 2 ^ (22 + 40 * 3199) := (Nat.pow_add 2 22 (40 * 3199)).symm
          _ = 2 ^ (40 * 3199 + 22) := by rw [Nat.add_comm 22 (40 * 3199)]
      calc (XSumNat j.val - 2 ^ (40 * j.val)) / 32003
          < 2 ^ (40 * 3199 + 21) := hQlt
        _ < 2 ^ (40 * 3199 + 22) := by
            have hpos : 0 < 2 ^ (40 * 3199 + 21) := pow_pos (by decide) _
            rw [show 40 * 3199 + 22 = (40 * 3199 + 21) + 1 from rfl, Nat.pow_succ]
            omega
        _ = 2 ^ 22 * (2 ^ 40) ^ 3199 := h22.symm
        _ ≤ 2 ^ 22 * (2 ^ 40) ^ i := Nat.mul_le_mul (le_refl _) hpow
    exact lt_of_le_of_lt hle hlt

/-! ### The matrix-product reduction -/

/-- The full product entry reduces to the sparse list sum over the pivot column. -/
theorem entry_sparse (k j : Fin 3199) :
    (Cinv * MS) k j
      = ((colDataNat j.val).map (fun t =>
          (BranchC.NoCarry.slot (2 ^ 40) k.val (CpkFunNat t.1) : ZMod 32003)
            * t.2)).sum := by
  rw [Matrix.mul_apply]
  have step1 : (∑ i : Fin 3199, Cinv k i * MS i j)
      = ∑ i : Fin 3199, ((colDataNat j.val).map
          (fun t => Cinv k i * (if t.1 = i.val then (t.2 : ZMod 32003) else 0))).sum := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [MS, mul_list_sum]
  rw [step1, finset_sum_list_sum]
  apply map_sum_congr
  intro t ht
  have ht1 : t.1 < 3199 := row_bound j t ht
  have inner : (∑ i : Fin 3199, Cinv k i *
      (if t.1 = i.val then (t.2 : ZMod 32003) else 0))
      = Cinv k ⟨t.1, ht1⟩ * t.2 := by
    have hconv : (∑ i : Fin 3199, Cinv k i *
        (if t.1 = i.val then (t.2 : ZMod 32003) else 0))
        = ∑ i : Fin 3199, (if ⟨t.1, ht1⟩ = i then Cinv k i * t.2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : t.1 = i.val
      · rw [if_pos h]
        have hi : (⟨t.1, ht1⟩ : Fin 3199) = i := Fin.ext h
        rw [if_pos hi]
      · have hi : ¬ (⟨t.1, ht1⟩ : Fin 3199) = i :=
          fun hcon => h (congrArg Fin.val hcon)
        rw [if_neg h, if_neg hi, mul_zero]
    rw [hconv, Finset.sum_ite_eq]
    simp
  rw [inner]
  rfl

/-! ### The bridge instantiation -/

/-- The bridge congruence for pivot column j at row k, in Nat form. -/
theorem bridge_entry (k j : Fin 3199) :
    ((termsFunNat j.val).map
      (fun t => t.1 * BranchC.NoCarry.slot (2 ^ 40) k.val t.2)).sum
      ≡ (if k.val = j.val then 1 else 0) [MOD 32003] := by
  apply BranchC.NoCarry.bridge (B := 2 ^ 40) (p := 32003) (by decide) (by decide)
    (terms := termsFunNat j.val) (X := XSumNat j.val)
    (Q := (XSumNat j.val - 2 ^ (40 * j.val)) / 32003) (j := j.val) (k := k.val)
  · exact hX_all j
  · -- the colOK equation, with 2^(40·j) rewritten as (2^40)^j
    have hM : BranchC.Mask.colOK j.val (XSumNat j.val) = true := colThm j
    unfold BranchC.Mask.colOK at hM
    rw [Bool.and_eq_true] at hM
    have heq : 32003 * ((XSumNat j.val - 2 ^ (40 * j.val)) / 32003)
        + 2 ^ (40 * j.val) = XSumNat j.val := beq_iff_eq.mp hM.1
    -- bridge wants B^j = (2^40)^j as the last term but Q in 2^(40·j)
    -- form, so rewrite the goal's (2^40)^j to 2^(40·j) and use heq raw.
    rw [← Nat.pow_mul]
    exact heq
  · -- the term-sum bound: at most 52 terms, each below 32002 · (2^15 − 1)
    intro i hi
    have hle : ((termsFunNat j.val).map
        (fun t => t.1 * BranchC.NoCarry.slot (2 ^ 40) i t.2)).sum
        ≤ (termsFunNat j.val).length * (32002 * (2 ^ 15 - 1)) := by
      apply sum_le
      intro t ht
      simp only [termsFunNat, List.mem_map] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      have hv : p.2 < 32003 := coeff_bound j p hp
      have hs : BranchC.NoCarry.slot (2 ^ 40) i (CpkFunNat p.1) < 2 ^ 15 :=
        slot_bounds ⟨p.1, row_bound j p hp⟩ i (by
          have hk := k.isLt
          omega)
      have h1 : p.2 ≤ 32002 := by omega
      have h2 : BranchC.NoCarry.slot (2 ^ 40) i (CpkFunNat p.1) ≤ 2 ^ 15 - 1 := by
        omega
      exact Nat.mul_le_mul h1 h2
    have hlen : (termsFunNat j.val).length ≤ 52 := by
      simp only [termsFunNat, List.length_map]
      exact length_bound j
    have hle2 := Nat.mul_le_mul hlen (le_refl (32002 * (2 ^ 15 - 1)))
    have hlt : 52 * (32002 * (2 ^ 15 - 1)) < 2 ^ 40 := by decide
    exact lt_of_le_of_lt (le_trans hle hle2) hlt
  · -- each term below 2^40
    intro t ht i hi
    simp only [termsFunNat, List.mem_map] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    have hv : p.2 < 32003 := coeff_bound j p hp
    have hs : BranchC.NoCarry.slot (2 ^ 40) i (CpkFunNat p.1) < 2 ^ 15 :=
      slot_bounds ⟨p.1, row_bound j p hp⟩ i (by
        have hk := k.isLt
        omega)
    have h1 : p.2 ≤ 32002 := by omega
    have h2 : BranchC.NoCarry.slot (2 ^ 40) i (CpkFunNat p.1) ≤ 2 ^ 15 - 1 := by
      omega
    have hle := Nat.mul_le_mul h1 h2
    have hlt : 32002 * (2 ^ 15 - 1) < 2 ^ 40 := by decide
    exact lt_of_le_of_lt hle hlt
  · -- Q's digits below 2^22, so 32003 · digit + 1 < 2^40
    intro i
    have hs := q_slots_all j i
    have h1 : BranchC.NoCarry.slot (2 ^ 40) i
        ((XSumNat j.val - 2 ^ (40 * j.val)) / 32003) ≤ 2 ^ 22 - 1 := by omega
    have hle : 32003 * BranchC.NoCarry.slot (2 ^ 40) i
        ((XSumNat j.val - 2 ^ (40 * j.val)) / 32003)
        ≤ 32003 * (2 ^ 22 - 1) := Nat.mul_le_mul (le_refl _) h1
    have hlt : 32003 * (2 ^ 22 - 1) + 1 < 2 ^ 40 := by decide
    exact lt_of_le_of_lt (Nat.add_le_add_right hle 1) hlt

/-! ### The matrix identity -/

/-- Casting a sparse ZMod sum back to the cast of the Nat sum. -/
theorem cast_list_sum (l : List (Nat × Nat)) (k : Nat) :
    ((l.map (fun t => (BranchC.NoCarry.slot (2 ^ 40) k (CpkFunNat t.1)
      : ZMod 32003) * t.2)).sum)
      = (((l.map (fun t => BranchC.NoCarry.slot (2 ^ 40) k (CpkFunNat t.1)
        * t.2)).sum : Nat) : ZMod 32003) := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, ih]

/-- A1: the packed inverse times the pivot block is the identity. -/
theorem A1 : Cinv * MS = 1 := by
  apply Matrix.ext
  intro k j
  rw [entry_sparse, cast_list_sum]
  have hsum : ((colDataNat j.val).map (fun t =>
      BranchC.NoCarry.slot (2 ^ 40) k.val (CpkFunNat t.1) * t.2)).sum
      = ((termsFunNat j.val).map
        (fun t => t.1 * BranchC.NoCarry.slot (2 ^ 40) k.val t.2)).sum := by
    rw [termsFunNat, List.map_map]
    apply map_sum_congr
    intro p _
    exact Nat.mul_comm _ _
  rw [hsum]
  have hmod := bridge_entry k j
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  rw [hmod, Matrix.one_apply]
  by_cases hkj : k = j
  · have hval : k.val = j.val := congrArg Fin.val hkj
    simp only [if_pos hval, if_pos hkj, Nat.cast_one]
  · have hval : ¬ (k.val = j.val) := fun hv => hkj (Fin.ext hv)
    simp only [if_neg hval, if_neg hkj, Nat.cast_zero]

#print axioms A1

end BranchC.A1Inst
