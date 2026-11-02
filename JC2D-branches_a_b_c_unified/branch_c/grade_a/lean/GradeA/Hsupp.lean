/- hsupp in Fpoly2 form: every monomial of `mult c · F_{gen c}` is a row.
   The Fpoly2 = Fpoly conversion happens at challenge_target assembly time
   (identical match arms, fin_cases + rfl).
   Weights (t, s, r, u, q) = (1, 2, 3, 3, 4); every generator satisfies
   maxTermDeg + maxMultDeg = 24 exactly, and every support q-exponent ≤ 5,
   so q⁶ = (0,0,0,0,6), the one degree-≤24 monomial missing from rowsList,
   never occurs. Membership goes by counting: rowsList ⊆ filtered box,
   both of length 3199, rowsList nodup.
   Reassembled 2026-11-02: the three killer decides (multDeg, multQ,
   filtered_length) are replaced by the kernel-verified split results
   (multDegRange, multQRange, filteredLength); all other theorems verbatim.
   Original three-decide version backed up at grade_a/logs/Hsupp.lean.2026-11-02.bak. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon
import GradeA.HsuppSplitMultDegAsm2
import GradeA.HsuppSplitMultQ
import GradeA.HsuppSplitFilteredInd2

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.Hsupp

open BranchC.A2Entry BranchC.A2Data BranchC.GradeA.Chart

/-- Weighted degree of a 5-tuple, weights (1,2,3,3,4). -/
def wdeg (t : Nat × Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2 * t.2.1 + 3 * t.2.2.1 + 3 * t.2.2.2.1 + 4 * t.2.2.2.2

/-- q-exponent of a 5-tuple. -/
def qexp (t : Nat × Nat × Nat × Nat × Nat) : Nat := t.2.2.2.2

theorem wdeg_add (a b : Nat × Nat × Nat × Nat × Nat) :
    wdeg (a + b) = wdeg a + wdeg b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp [wdeg]
  omega

theorem qexp_add (a b : Nat × Nat × Nat × Nat × Nat) :
    qexp (a + b) = qexp a + qexp b := rfl

/-- Support of `polyOfTerms` is contained in the term monomials. -/
theorem support_polyOfTerms (l : List Term) :
    (polyOfTerms l).support ⊆ (l.map Term.mono).toFinset := by
  induction l with
  | nil => simp [polyOfTerms]
  | cons t ts ih =>
    show (t.poly + polyOfTerms ts).support ⊆ (t.mono :: ts.map Term.mono).toFinset
    intro d hd
    rcases Finset.mem_union.mp (Finsupp.support_add hd) with h | h
    · have hmono : d ∈ ({t.mono} : Finset (Fin 5 →₀ ℕ)) :=
        MvPolynomial.support_monomial_subset h
      rw [Finset.mem_singleton] at hmono
      rw [hmono, List.mem_toFinset]
      exact List.mem_cons_self
    · have hmem : d ∈ (ts.map Term.mono).toFinset := ih h
      rw [List.mem_toFinset] at hmem ⊢
      exact List.mem_cons_of_mem _ hmem

/-- Support decomposition: a support monomial of `mult c · F_{gen c}` is
    `multMono c + t.mono` for a term `t` of the generator. -/
theorem support_decomp (c : Fin 3199) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (MvPolynomial.monomial (multMono c) (1 : Polynomial ℤ) *
      Fpoly2 (genFun c)).support) :
    ∃ t ∈ tlFun (genFun c), d = multMono c + t.mono := by
  rw [Fpoly2_tlFun] at hd
  have hmul := MvPolynomial.support_mul
    (MvPolynomial.monomial (multMono c) (1 : Polynomial ℤ)) (polyOfTerms (tlFun (genFun c))) hd
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hmul
  have ha' : a = multMono c := by
    simpa [MvPolynomial.support_monomial] using ha
  have hb' : b ∈ (tlFun (genFun c)).map Term.mono := by
    have := support_polyOfTerms (tlFun (genFun c)) hb
    exact List.mem_toFinset.mp this
  obtain ⟨t, ht, hmono⟩ := List.mem_map.mp hb'
  exact ⟨t, ht, by rw [← hab, ha', hmono]⟩

/-- Per-generator term degree bound (5, 6, 6, 7, 7, 7). -/
theorem termDeg (g : Fin 6) :
    ∀ t ∈ tlFun g, wdeg (mono5 t) ≤
      (if g = 0 then 5 else if g = 1 then 6 else if g = 2 then 6 else 7) := by
  fin_cases g <;> decide

/-- Per-generator term q-exponent bound (1). -/
theorem termQ (g : Fin 6) : ∀ t ∈ tlFun g, qexp (mono5 t) ≤ 1 := by
  fin_cases g <;> decide

/-- Per-column multiplier degree bound, via the split range statement. -/
theorem multDeg (c : Fin 3199) :
    wdeg (multTuple c) ≤
      (if genFun c = 0 then 19 else if genFun c = 1 then 18
        else if genFun c = 2 then 18 else 17) :=
  BranchC.HsuppSplit.multDegRange c.val (List.mem_range.mpr c.isLt)

/-- Per-column multiplier q-exponent bound (4), via the split range statement. -/
theorem multQ (c : Fin 3199) : qexp (multTuple c) ≤ 4 :=
  BranchC.HsuppSplit.multQRange c.val (List.mem_range.mpr c.isLt)

/-- Term + multiplier degree bounds sum to 24 for every generator. -/
theorem bound_sum (g : Fin 6) :
    (if g = 0 then 5 else if g = 1 then 6 else if g = 2 then 6 else 7) +
      (if g = 0 then 19 else if g = 1 then 18 else if g = 2 then 18 else 17) = 24 := by
  fin_cases g <;> decide

theorem rows_length : rowsList.length = 3199 := by decide

/-- The box of all tuples with components in range. -/
def boxList : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 25).flatMap (fun t =>
    (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (t, s, r, u, q))))))

/-- The box filtered to degree ≤ 24 and q-exponent ≠ 6. -/
def filteredList : List (Nat × Nat × Nat × Nat × Nat) :=
  boxList.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))

/-- Filtered box length, via the split induction file. -/
theorem filtered_length : filteredList.length = 3199 :=
  BranchC.HsuppSplit.filteredLength

/-- A tuple with degree ≤ 24 and q-exponent ≠ 6 is in the filtered box. -/
theorem filtered_mem_of_bounds (u : Nat × Nat × Nat × Nat × Nat)
    (hdeg : wdeg u ≤ 24) (hq : qexp u ≠ 6) : u ∈ filteredList := by
  have hbox : u ∈ boxList := by
    obtain ⟨t, s, r, v, q⟩ := u
    simp only [wdeg] at hdeg
    have ht : t < 25 := by omega
    have hs : s < 13 := by omega
    have hr : r < 9 := by omega
    have hv : v < 9 := by omega
    have hq' : q < 7 := by omega
    simp only [boxList, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨t, ht, s, hs, r, hr, v, hv, q, hq', rfl⟩
  rw [filteredList, List.mem_filter]
  exact ⟨hbox, by simp [hdeg, hq]⟩

/-- Every row is in the filtered box. -/
theorem rows_subset_filtered : rowsList ⊆ filteredList := by
  intro u hu
  have hdeg : wdeg u ≤ 24 := by
    have hall : (rowsList.map wdeg).all (fun n => decide (n ≤ 24)) = true := by decide
    have hmem := (List.all_eq_true.mp hall) (wdeg u) (List.mem_map_of_mem hu)
    exact of_decide_eq_true hmem
  have hq : qexp u ≠ 6 := by
    have hall : (rowsList.map qexp).all (fun n => decide (n ≠ 6)) = true := by decide
    have hmem := (List.all_eq_true.mp hall) (qexp u) (List.mem_map_of_mem hu)
    exact of_decide_eq_true hmem
  exact filtered_mem_of_bounds u hdeg hq

/-- The counting step: degree ≤ 24 and q-exponent ≠ 6 imply membership in rows. -/
theorem mem_of_bounds (u : Nat × Nat × Nat × Nat × Nat)
    (hdeg : wdeg u ≤ 24) (hq : qexp u ≠ 6) : u ∈ rowsList := by
  by_contra hu
  have hnd : (rowsList ++ [u]).Nodup := by
    rw [List.nodup_append]
    refine ⟨BranchC.A2Check.rowsNodup, List.nodup_singleton u, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    exact hu (by rw [← hb, ← hab]; exact ha)
  have hsub : rowsList ++ [u] ⊆ filteredList := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact rows_subset_filtered hx
    · rw [List.mem_singleton] at hx
      rw [hx]
      exact filtered_mem_of_bounds u hdeg hq
  have hle := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_append, List.length_singleton, rows_length, filtered_length] at hle
  omega

/-- hsupp in Fpoly2 form. -/
theorem hsupp2 (c : Fin 3199) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (MvPolynomial.monomial (multMono c) (1 : Polynomial ℤ) *
      Fpoly2 (genFun c)).support) :
    d ∈ Set.range rowMono := by
  obtain ⟨t, ht, hdt⟩ := support_decomp c d hd
  have hsum : d = finsuppOfTuple (multTuple c + mono5 t) := by
    simp only [hdt, multMono, mono_finsuppOfTuple]
    exact (finsuppOfTuple_add _ _).symm
  have hdeg : wdeg (multTuple c + mono5 t) ≤ 24 := by
    rw [wdeg_add]
    have hm := multDeg c
    have htm := termDeg (genFun c) t ht
    have hs := bound_sum (genFun c)
    omega
  have hq : qexp (multTuple c + mono5 t) ≠ 6 := by
    rw [qexp_add]
    have hm := multQ c
    have htm := termQ (genFun c) t ht
    omega
  have hmem := mem_of_bounds (multTuple c + mono5 t) hdeg hq
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < 3199 := by rw [rows_length] at hi; exact hi
  have hr : rowTuple ⟨i, hi'⟩ = multTuple c + mono5 t := by
    show rowsList.getD i (0, 0, 0, 0, 0) = multTuple c + mono5 t
    rw [List.getD_eq_getElem rowsList (0, 0, 0, 0, 0) hi]
    exact hget
  refine ⟨⟨i, hi'⟩, ?_⟩
  simp only [rowMono]
  rw [hr]
  exact hsum.symm

end BranchC.Hsupp
