/- A2 tuple-check chunk 206b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk206b : (2065 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk206b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2065 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2065) boundChunk206b⟩)).all (checkFun ⟨2065 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2065) boundChunk206b⟩) = true ∧ linkFun ⟨2065 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2065) boundChunk206b⟩ = true := by
  decide +kernel

end BranchC.A2Check
