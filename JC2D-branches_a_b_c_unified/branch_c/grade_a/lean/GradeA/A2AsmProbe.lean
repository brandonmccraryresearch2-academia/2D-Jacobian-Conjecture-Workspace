/- Assembly probes: risky bridge pieces for A2Assembly, each small. -/
import GradeA.A2Entry
import GradeA.A2TupleCheckAsm
import GradeA.A1Instantiation
import GradeA.A2Terms
import GradeA.A2Data
import GradeA.A2RowsNodup

open BranchC.GradeA.Chart BranchC.A2Terms

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem rowsList_length_probe : BranchC.A2Data.rowsList.length = 3199 := by decide

example (a b : Nat × Nat × Nat × Nat × Nat) :
    BranchC.A2Check.add5 a b = a + b := rfl

noncomputable def toChartTerm (t : A2Term) : Term :=
  ⟨t.c, t.i, t.et, t.es, t.er, t.eu, t.eq⟩

example : (tlPsi.map toChartTerm) = tl_Psi := rfl
example : (tlPhi1.map toChartTerm) = tl_Phi1 := rfl
example : (tlPhi2.map toChartTerm) = tl_Phi2 := rfl
example : (tlTheta1.map toChartTerm) = tl_Theta1 := rfl
example : (tlTheta2.map toChartTerm) = tl_Theta2 := rfl
example : (tlTheta3.map toChartTerm) = tl_Theta3 := rfl

example (t : A2Term) :
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

example (n : Nat) (hn : n < 3199) (r : Fin 3199) :
    BranchC.A2Check.rowTupleOfNat n = BranchC.A2Data.rowTuple r ↔
      n = r.val := by
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

example : Fact (Nat.Prime 32003) := ⟨by norm_num⟩

example (MS : Matrix (Fin 3199) (Fin 3199) (ZMod 32003))
    (d : Fin 3199 → ZMod 32003) (r c : Fin 3199) :
    (MS * Matrix.diagonal d) r c = MS r c * d c := by
  simp [Matrix.mul_apply, Matrix.diagonal]
