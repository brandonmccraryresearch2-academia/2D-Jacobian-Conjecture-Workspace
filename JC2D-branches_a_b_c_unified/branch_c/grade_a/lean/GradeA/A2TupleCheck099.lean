/- A2 tuple-check chunk 99 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk99 : (990 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk99 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 990) boundChunk99⟩)).all (checkFun ⟨990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 990) boundChunk99⟩) = true ∧ linkFun ⟨990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 990) boundChunk99⟩ = true := by
  decide +kernel

end BranchC.A2Check
