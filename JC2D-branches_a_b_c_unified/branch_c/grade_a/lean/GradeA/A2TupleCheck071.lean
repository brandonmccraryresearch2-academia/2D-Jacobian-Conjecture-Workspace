/- A2 tuple-check chunk 71 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk71 : (710 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk71 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨710 + j, Nat.lt_trans (Nat.add_lt_add_left hj 710) boundChunk71⟩)).all (checkFun ⟨710 + j, Nat.lt_trans (Nat.add_lt_add_left hj 710) boundChunk71⟩) = true ∧ linkFun ⟨710 + j, Nat.lt_trans (Nat.add_lt_add_left hj 710) boundChunk71⟩ = true := by
  decide +kernel

end BranchC.A2Check
