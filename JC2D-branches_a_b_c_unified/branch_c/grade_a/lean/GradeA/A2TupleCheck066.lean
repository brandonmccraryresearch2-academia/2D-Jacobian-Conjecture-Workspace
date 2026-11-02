/- A2 tuple-check chunk 66 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk66 : (660 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk66 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 660) boundChunk66⟩)).all (checkFun ⟨660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 660) boundChunk66⟩) = true ∧ linkFun ⟨660 + j, Nat.lt_trans (Nat.add_lt_add_left hj 660) boundChunk66⟩ = true := by
  decide +kernel

end BranchC.A2Check
