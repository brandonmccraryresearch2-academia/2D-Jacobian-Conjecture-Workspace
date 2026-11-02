/- A2 tuple-check chunk 108 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk108 : (1080 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk108 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1080 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1080) boundChunk108⟩)).all (checkFun ⟨1080 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1080) boundChunk108⟩) = true ∧ linkFun ⟨1080 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1080) boundChunk108⟩ = true := by
  decide +kernel

end BranchC.A2Check
