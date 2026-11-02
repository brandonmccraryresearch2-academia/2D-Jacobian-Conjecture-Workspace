/- A2 tuple-check chunk 237b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk237b : (2375 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk237b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2375 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2375) boundChunk237b⟩)).all (checkFun ⟨2375 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2375) boundChunk237b⟩) = true ∧ linkFun ⟨2375 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2375) boundChunk237b⟩ = true := by
  decide +kernel

end BranchC.A2Check
