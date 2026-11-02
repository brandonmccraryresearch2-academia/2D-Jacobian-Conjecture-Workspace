/- A2 tuple-check chunk 208a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk208a : (2080 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk208a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2080 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2080) boundChunk208a⟩)).all (checkFun ⟨2080 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2080) boundChunk208a⟩) = true ∧ linkFun ⟨2080 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2080) boundChunk208a⟩ = true := by
  decide +kernel

end BranchC.A2Check
