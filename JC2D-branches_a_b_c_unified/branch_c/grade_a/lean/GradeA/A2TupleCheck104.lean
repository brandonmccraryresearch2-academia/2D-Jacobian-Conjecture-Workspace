/- A2 tuple-check chunk 104 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk104 : (1040 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk104 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1040 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1040) boundChunk104⟩)).all (checkFun ⟨1040 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1040) boundChunk104⟩) = true ∧ linkFun ⟨1040 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1040) boundChunk104⟩ = true := by
  decide +kernel

end BranchC.A2Check
