/- A2 assembly: the evaluated Macaulay block equals MS times the diagonal scale.
   Main theorem A2 is stated with A2Entry's Fpoly2 (the Fpoly = Fpoly2 bridge
   is deferred to the challenge_target assembly, which needs Chart.Main built). -/
import GradeA.A2Entry
import GradeA.A2TupleCheckAsm
import GradeA.A1Instantiation
import GradeA.A1Data
import GradeA.A2Terms
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.Macaulay

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Assembly

/-- Mirror an A2Term into a Chart Term (structures are field-identical). -/
noncomputable def toChartTerm (t : BranchC.A2Terms.A2Term) : BranchC.GradeA.Chart.Term :=
  ⟨t.c, t.i, t.et, t.es, t.er, t.eu, t.eq⟩

theorem mono5_toChart (t : BranchC.A2Terms.A2Term) :
    BranchC.A2Entry.mono5 (toChartTerm t) = BranchC.A2Terms.mono5 t := rfl

theorem add5_eq (a b : Nat × Nat × Nat × Nat × Nat) :
    BranchC.A2Check.add5 a b = a + b := rfl

theorem cond_iff (t : BranchC.A2Terms.A2Term)
    (mult row : Nat × Nat × Nat × Nat × Nat) :
    (BranchC.A2Entry.mono5 (toChartTerm t) + mult = row) ↔
    (BranchC.A2Check.add5 (BranchC.A2Terms.mono5 t) mult = row) := by
  simp only [mono5_toChart, add5_eq]

theorem termValNat_cast (t : BranchC.A2Terms.A2Term) :
    ((BranchC.A2Terms.termValNat t : ℕ) : ZMod 32003) =
      BranchC.A2Entry.evalTerm (toChartTerm t) := by
  have hnn : 0 ≤ t.c % 32003 := Int.emod_nonneg _ (by norm_num)
  have hA : (((t.c % 32003).toNat : ℕ) : ZMod 32003) = (t.c : ZMod 32003) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    exact ZMod.intCast_mod t.c 32003
  have hB : (((11147 ^ t.i % 32003 : ℕ)) : ZMod 32003) =
      (11147 : ZMod 32003) ^ t.i := by
    rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]
  simp only [BranchC.A2Terms.termValNat, BranchC.A2Entry.evalTerm, toChartTerm]
  rw [ZMod.natCast_mod, Nat.cast_mul, hA, hB]

/-- Cast of a mapped sum over a term list: Chart side equals cast of Nat side. -/
theorem sum_cast (l : List BranchC.A2Terms.A2Term)
    (mult row : Nat × Nat × Nat × Nat × Nat) :
    ((l.map (fun t => if BranchC.A2Entry.mono5 (toChartTerm t) + mult = row then
      BranchC.A2Entry.evalTerm (toChartTerm t) else 0)).sum)
    = (((l.map (fun t => if BranchC.A2Check.add5 (BranchC.A2Terms.mono5 t) mult = row then
      BranchC.A2Terms.termValNat t else 0)).sum : ℕ) : ZMod 32003) := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases h : BranchC.A2Check.add5 (BranchC.A2Terms.mono5 t) mult = row
    · have hC : BranchC.A2Entry.mono5 (toChartTerm t) + mult = row :=
        (cond_iff t mult row).mpr h
      rw [if_pos hC, if_pos h, Nat.cast_add, termValNat_cast, ih]
    · have hC : ¬ (BranchC.A2Entry.mono5 (toChartTerm t) + mult = row) :=
        fun hc => h ((cond_iff t mult row).mp hc)
      rw [if_neg hC, if_neg h, Nat.cast_add, Nat.cast_zero, zero_add, zero_add, ih]

/-- The A2Term generator lists map through toChartTerm onto the Chart lists. -/
theorem tlFun_map (n : Fin 6) :
    ((BranchC.A2Terms.tlFun n).map toChartTerm) = BranchC.A2Entry.tlFun n := by
  fin_cases n <;> rfl

/-- tupleSum (Chart side) is the cast of tupleSumNatT (Nat side). -/
theorem tupleSum_cast (c r : Fin 3199) :
    BranchC.A2Entry.tupleSum c r =
      ((BranchC.A2Check.tupleSumNatT c (BranchC.A2Data.rowTuple r) : ℕ) : ZMod 32003) := by
  simp only [BranchC.A2Entry.tupleSum, BranchC.A2Check.tupleSumNatT,
    BranchC.A2Entry.colTerms, BranchC.A2Check.colTermsNat]
  rw [← tlFun_map (BranchC.A2Data.genFun c), List.map_map]
  exact sum_cast (BranchC.A2Terms.tlFun (BranchC.A2Data.genFun c))
    (BranchC.A2Data.multTuple c) (BranchC.A2Data.rowTuple r)

/-- Row-tuple equality is index equality, via rowsList.Nodup. -/
theorem rowTuple_iff (n : Nat) (hn : n < 3199) (r : Fin 3199) :
    BranchC.A2Check.rowTupleOfNat n = BranchC.A2Data.rowTuple r ↔ n = r.val := by
  have hlen : BranchC.A2Data.rowsList.length = 3199 := by decide
  have e1 : BranchC.A2Data.rowsList.getD n (0, 0, 0, 0, 0) =
      BranchC.A2Data.rowsList[n]'(by omega) :=
    List.getD_eq_getElem BranchC.A2Data.rowsList (0, 0, 0, 0, 0) (by omega)
  have e2 : BranchC.A2Data.rowsList.getD r.val (0, 0, 0, 0, 0) =
      BranchC.A2Data.rowsList[r.val]'(by omega) :=
    List.getD_eq_getElem BranchC.A2Data.rowsList (0, 0, 0, 0, 0) (by omega)
  simp only [BranchC.A2Check.rowTupleOfNat, BranchC.A2Data.rowTuple]
  rw [e1, e2]
  exact BranchC.A2Check.rowsNodup.getElem_inj_iff

/-- Casting a mapped Nat sum to ZMod, given a per-element cast equality. -/
theorem cast_map_sum (f : Nat × Nat → ℕ) (g : Nat × Nat → ZMod 32003) :
    ∀ (l : List (Nat × Nat)), (∀ t ∈ l, ((f t : ℕ) : ZMod 32003) = g t) →
      (((l.map f).sum : ℕ) : ZMod 32003) = (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons t ts ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add, h t List.mem_cons_self,
      ih (fun t' ht' => h t' (List.mem_cons_of_mem t ht'))]

/-- The cast MS-entry: msValNatT at a row tuple equals MS at that row. -/
theorem ms_entry (c r : Fin 3199) :
    ((BranchC.A2Check.msValNatT c (BranchC.A2Data.rowTuple r) : ℕ) : ZMod 32003) =
      BranchC.A1Inst.MS r c := by
  simp only [BranchC.A2Check.msValNatT, BranchC.A1Inst.MS]
  rw [BranchC.A2Check.linkAll c, List.map_map]
  exact cast_map_sum
    (fun t => if BranchC.A2Check.rowTupleOfNat t.1 = BranchC.A2Data.rowTuple r then
      t.2 else 0)
    (fun t => if t.1 = r.val then (t.2 : ZMod 32003) else 0)
    (BranchC.A1Data.colDataNat c.val)
    (by
      intro t ht
      show ((if BranchC.A2Check.rowTupleOfNat t.1 = BranchC.A2Data.rowTuple r then
        t.2 else 0 : ℕ) : ZMod 32003) =
        (if t.1 = r.val then (t.2 : ZMod 32003) else 0)
      have hb : t.1 < 3199 := BranchC.A1Inst.row_bound c t ht
      by_cases h : BranchC.A2Check.rowTupleOfNat t.1 = BranchC.A2Data.rowTuple r
      · rw [if_pos h, if_pos ((rowTuple_iff t.1 hb r).mp h)]
      · have h2 : ¬ (t.1 = r.val) := fun he => h ((rowTuple_iff t.1 hb r).mpr he)
        rw [if_neg h, if_neg h2, Nat.cast_zero])

/-- The column check, cast to ZMod: tupleSumNatT equals msValNatT times scale. -/
theorem column_nat (c r : Fin 3199) :
    ((BranchC.A2Check.tupleSumNatT c (BranchC.A2Data.rowTuple r) : ℕ) : ZMod 32003)
    = ((BranchC.A2Check.msValNatT c (BranchC.A2Data.rowTuple r) : ℕ) : ZMod 32003)
      * (BranchC.A2Data.scaleFun (BranchC.A2Data.genFun c) : ZMod 32003) := by
  by_cases h : BranchC.A2Data.rowTuple r ∈ BranchC.A2Check.unionTuples c
  · have h1 : ((BranchC.A2Check.tupleSumNatT c (BranchC.A2Data.rowTuple r) : ℕ) : ZMod 32003)
        = ((BranchC.A2Check.msValNatT c (BranchC.A2Data.rowTuple r) *
          BranchC.A2Data.scaleFun (BranchC.A2Data.genFun c) : ℕ) : ZMod 32003) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact BranchC.A2Check.colCheck c (BranchC.A2Data.rowTuple r) h
    rw [h1, Nat.cast_mul]
  · have hcomp : BranchC.A2Data.rowTuple r ∉ BranchC.A2Check.computedTuples c := by
      intro hc
      apply h
      simp only [BranchC.A2Check.unionTuples]
      exact List.mem_append.mpr (Or.inl hc)
    have hms : BranchC.A2Data.rowTuple r ∉
        (BranchC.A2MSPairs.msTuplePairs c.val).map Prod.fst := by
      intro hc
      apply h
      simp only [BranchC.A2Check.unionTuples]
      exact List.mem_append.mpr (Or.inr hc)
    rw [BranchC.A2Check.tupleSumNatT_zero c _ hcomp,
      BranchC.A2Check.msValNatT_zero c _ hms, Nat.cast_zero, zero_mul]

/-- One column entry: tupleSum equals MS times the diagonal scale. -/
theorem column_entry (c r : Fin 3199) :
    BranchC.A2Entry.tupleSum c r =
      BranchC.A1Inst.MS r c *
        (BranchC.A2Data.scaleFun (BranchC.A2Data.genFun c) : ZMod 32003) := by
  rw [tupleSum_cast c r, column_nat c r, ms_entry c r]

theorem diagonal_entry (MS : Matrix (Fin 3199) (Fin 3199) (ZMod 32003))
    (d : Fin 3199 → ZMod 32003) (r c : Fin 3199) :
    (MS * Matrix.diagonal d) r c = MS r c * d c := by
  simp [Matrix.mul_apply, Matrix.diagonal]

/-- A2: the evaluated Macaulay block is MS times the diagonal scale matrix. -/
theorem A2 :
    (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147).mapMatrix
      (BranchC.GradeA.macaulay BranchC.A2Entry.Fpoly2 BranchC.A2Entry.rowMono
        BranchC.A2Data.genFun BranchC.A2Entry.multMono)
    = BranchC.A1Inst.MS * Matrix.diagonal
      (fun c => (BranchC.A2Data.scaleFun (BranchC.A2Data.genFun c) : ZMod 32003)) := by
  ext r c
  rw [BranchC.A2Entry.evaluatedEntry r c]
  rw [diagonal_entry BranchC.A1Inst.MS
    (fun c => (BranchC.A2Data.scaleFun (BranchC.A2Data.genFun c) : ZMod 32003)) r c]
  exact column_entry c r

#print axioms A2

end BranchC.A2Assembly
