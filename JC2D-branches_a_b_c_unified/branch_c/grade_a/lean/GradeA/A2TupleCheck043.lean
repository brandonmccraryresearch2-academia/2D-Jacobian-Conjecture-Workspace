/- A2 tuple-check chunk 43 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk43 : (430 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk43 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 430) boundChunk43⟩)).all (checkFun ⟨430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 430) boundChunk43⟩) = true ∧ linkFun ⟨430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 430) boundChunk43⟩ = true := by
  decide +kernel

end BranchC.A2Check
