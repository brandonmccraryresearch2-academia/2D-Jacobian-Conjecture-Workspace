/- A2 tuple-check chunk 224b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk224b : (2245 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk224b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2245 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2245) boundChunk224b⟩)).all (checkFun ⟨2245 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2245) boundChunk224b⟩) = true ∧ linkFun ⟨2245 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2245) boundChunk224b⟩ = true := by
  decide +kernel

end BranchC.A2Check
