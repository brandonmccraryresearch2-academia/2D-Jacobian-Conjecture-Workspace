/- A2 tuple-check chunk 210b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk210b : (2105 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk210b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2105 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2105) boundChunk210b⟩)).all (checkFun ⟨2105 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2105) boundChunk210b⟩) = true ∧ linkFun ⟨2105 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2105) boundChunk210b⟩ = true := by
  decide +kernel

end BranchC.A2Check
