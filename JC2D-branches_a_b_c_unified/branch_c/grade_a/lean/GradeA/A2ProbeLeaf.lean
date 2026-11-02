import GradeA.A2ProbeNatChunk090
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
theorem probeLeafLit : (dedup5 (unionTuples ⟨905, by decide⟩)).all (checkFun ⟨905, by decide⟩) = true ∧ linkFun ⟨905, by decide⟩ = true := by
  exact probeNatChunk090 5 (by decide)
theorem probeLeafGen (c : Fin 3199) (hlo : 900 ≤ c.val) (hhi : c.val < 910) :
    (dedup5 (unionTuples c)).all (checkFun c) = true ∧ linkFun c = true := by
  have hj : c.val - 900 < 10 := Nat.sub_lt_left_of_lt_add hlo hhi
  have hck := probeNatChunk090 (c.val - 900) hj
  have hval : 900 + (c.val - 900) = c.val := Nat.add_sub_cancel' hlo
  have hce : (⟨900 + (c.val - 900), Nat.lt_trans (Nat.add_lt_add_left hj 900) boundChunk090⟩ : Fin 3199) = c := Fin.ext hval
  rw [hce] at hck
  exact hck
end BranchC.A2Check
