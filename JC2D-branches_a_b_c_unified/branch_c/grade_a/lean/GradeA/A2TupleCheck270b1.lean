/- A2 tuple-check chunk 270b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk270b1 : (2705 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk270b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2705 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2705) boundChunk270b1⟩)).all (checkFun ⟨2705 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2705) boundChunk270b1⟩) = true ∧ linkFun ⟨2705 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2705) boundChunk270b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
