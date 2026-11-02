/- A2 tuple-check chunk 218b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk218b : (2185 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk218b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2185) boundChunk218b⟩)).all (checkFun ⟨2185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2185) boundChunk218b⟩) = true ∧ linkFun ⟨2185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2185) boundChunk218b⟩ = true := by
  decide +kernel

end BranchC.A2Check
