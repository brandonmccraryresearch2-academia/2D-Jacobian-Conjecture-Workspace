/- A2 tuple-check chunk 67 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk67 : (670 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk67 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨670 + j, Nat.lt_trans (Nat.add_lt_add_left hj 670) boundChunk67⟩)).all (checkFun ⟨670 + j, Nat.lt_trans (Nat.add_lt_add_left hj 670) boundChunk67⟩) = true ∧ linkFun ⟨670 + j, Nat.lt_trans (Nat.add_lt_add_left hj 670) boundChunk67⟩ = true := by
  decide +kernel

end BranchC.A2Check
