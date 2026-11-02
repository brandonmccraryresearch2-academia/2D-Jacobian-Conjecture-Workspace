/- Data hypotheses for chartEmptyC_T1ne0_of_certificate at the concrete data
   (ρ = Fin 3199, p = 32003, mon = rowMono, gen = genFun, mult = multMono,
   w₀ = 11147, MS = A1Inst.MS, scale = cast of scaleFun).
   hsupp is NOT in this file: it needs Fpoly (Chart.Assembly), whose import
   tree (Chart.Main, T1Zero.Combine, Descent2R) belongs to the phase-3 build.
   The Fpoly bridge and the hsupp statement conversion happen at assembly time. -/
import GradeA.A2Entry
import GradeA.A2RowsNodup
import GradeA.A2Data
import GradeA.IrreducibleR

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.DataHypotheses

/-- hw₀: 11147 is a root of Rint mod 32003. -/
theorem hw₀ :
    Polynomial.eval₂ (Int.castRingHom (ZMod 32003)) 11147 BranchC.GradeA.Rint = 0 := by
  -- simp evaluates the LHS to the integer value R(11147); that value is 0 mod 32003.
  have h : Polynomial.eval₂ (Int.castRingHom (ZMod 32003)) 11147 BranchC.GradeA.Rint
      = (172088184832896567048 : ZMod 32003) := by
    simp [BranchC.GradeA.Rint]
  rw [h]
  decide

/-- hscale: every generator scale is nonzero mod 32003. -/
theorem hscale : ∀ n : Fin 6, (BranchC.A2Data.scaleFun n : ZMod 32003) ≠ 0 := by
  intro n
  fin_cases n <;> decide

/-- Primality of 32003 (needed as a Fact instance at assembly time). -/
theorem prime32003 : Fact (Nat.Prime 32003) := ⟨by norm_num⟩

/-- Row tuples are injective, via rowsList.Nodup. -/
theorem rowTuple_injective : Function.Injective BranchC.A2Data.rowTuple := by
  intro a b hab
  have hlen : BranchC.A2Data.rowsList.length = 3199 := by decide
  have e1 : BranchC.A2Data.rowsList.getD a.val (0, 0, 0, 0, 0) =
      BranchC.A2Data.rowsList[a.val]'(by omega) :=
    List.getD_eq_getElem BranchC.A2Data.rowsList (0, 0, 0, 0, 0) (by omega)
  have e2 : BranchC.A2Data.rowsList.getD b.val (0, 0, 0, 0, 0) =
      BranchC.A2Data.rowsList[b.val]'(by omega) :=
    List.getD_eq_getElem BranchC.A2Data.rowsList (0, 0, 0, 0, 0) (by omega)
  simp only [BranchC.A2Data.rowTuple] at hab
  rw [e1, e2] at hab
  have hval : a.val = b.val := (BranchC.A2Check.rowsNodup.getElem_inj_iff).mp hab
  exact Fin.ext hval

/-- hmon: the row monomials are injective. -/
theorem hmon : Function.Injective BranchC.A2Entry.rowMono := by
  intro a b hab
  simp only [BranchC.A2Entry.rowMono] at hab
  exact rowTuple_injective (BranchC.A2Entry.finsuppOfTuple_injective hab)

/-- hr₁: the monomial 1 (zero tuple, rowsList index 19) is among the rows. -/
theorem hr₁ : BranchC.A2Entry.rowMono ⟨19, by decide⟩ = 0 := by
  have h19 : BranchC.A2Data.rowTuple ⟨19, by decide⟩ = (0, 0, 0, 0, 0) := by
    simp only [BranchC.A2Data.rowTuple]
    rw [List.getD_eq_getElem BranchC.A2Data.rowsList (0, 0, 0, 0, 0) (by decide)]
    decide
  simp only [BranchC.A2Entry.rowMono, h19]
  ext i
  fin_cases i <;> simp [BranchC.A2Entry.finsuppOfTuple]

end BranchC.DataHypotheses
