/- Scratch attempt (2026-11-04): Fpoly = Fpoly2 bridge + challenge_target
   instantiation. NOT part of the repo tree; run with `lake env lean` from
   the grade_a project dir on lean-build-2, olean to /tmp. -/

import GradeA.Chart.Assembly
import GradeA.A2Assembly
import GradeA.A1Instantiation
import GradeA.DataHypotheses
import GradeA.Hsupp

/-- Bridge: the chart `Fpoly` and the comparator's `Fpoly2` are the same six
    `polyOfTerms` generators in the same order (0=Psi, 1=Phi1, 2=Phi2,
    3=Theta1, 4=Theta2, 5=Theta3), built from the single `tl_*` definitions
    in `Chart/Gens.lean`. -/
theorem bridge_Fpoly :
    BranchC.GradeA.Chart.Fpoly = BranchC.A2Entry.Fpoly2 := by
  funext n
  fin_cases n <;> rfl

/-- `hsupp2` transported from `Fpoly2` to `Fpoly` along the bridge, in exactly
    the form `chartEmptyC_T1ne0_of_certificate` wants. -/
theorem hsupp_chart (c : Fin 3199) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (MvPolynomial.monomial (BranchC.A2Entry.multMono c) (1 : Polynomial ℤ) *
      BranchC.GradeA.Chart.Fpoly (BranchC.A2Data.genFun c)).support) :
    d ∈ Set.range BranchC.A2Entry.rowMono := by
  rw [bridge_Fpoly] at hd
  exact BranchC.Hsupp.hsupp2 c d hd

/-- A2 transported from `Fpoly2` to `Fpoly` along the bridge. -/
theorem hA2_chart :
    (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147).mapMatrix
      (BranchC.GradeA.macaulay BranchC.GradeA.Chart.Fpoly BranchC.A2Entry.rowMono
        BranchC.A2Data.genFun BranchC.A2Entry.multMono)
    = BranchC.A1Inst.MS * Matrix.diagonal
      (fun c => (BranchC.A2Data.scaleFun (BranchC.A2Data.genFun c) : ZMod 32003)) := by
  have h := BranchC.A2Assembly.A2
  rw [← bridge_Fpoly] at h
  exact h

/-- challenge_target: `ChartEmptyC_T1ne0 L` for every field of characteristic 0,
    with no hypotheses — the interface instantiated at the concrete data
    (ρ = Fin 3199, p = 32003, w₀ = 11147). -/
theorem challenge_target {L : Type*} [Field L] [CharZero L] :
    BranchC.ChartEmptyC_T1ne0 L := by
  haveI := BranchC.DataHypotheses.prime32003
  exact BranchC.GradeA.Chart.chartEmptyC_T1ne0_of_certificate
    BranchC.A2Entry.rowMono BranchC.DataHypotheses.hmon ⟨19, by decide⟩
    BranchC.DataHypotheses.hr₁ BranchC.A2Data.genFun BranchC.A2Entry.multMono
    hsupp_chart 11147 BranchC.DataHypotheses.hw₀
    BranchC.A1Inst.MS BranchC.A1Inst.Cinv
    (fun n => (BranchC.A2Data.scaleFun n : ZMod 32003))
    BranchC.DataHypotheses.hscale BranchC.A1Inst.A1 hA2_chart L

#print axioms challenge_target
