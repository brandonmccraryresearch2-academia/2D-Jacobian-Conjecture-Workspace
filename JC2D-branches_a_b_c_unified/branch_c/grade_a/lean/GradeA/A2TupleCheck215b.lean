/- A2 tuple-check chunk 215b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk215b : (2155 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk215b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2155) boundChunk215b⟩)).all (checkFun ⟨2155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2155) boundChunk215b⟩) = true ∧ linkFun ⟨2155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2155) boundChunk215b⟩ = true := by
  decide +kernel

end BranchC.A2Check
