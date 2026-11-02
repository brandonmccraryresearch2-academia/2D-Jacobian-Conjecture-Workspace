/- A2 tuple-check chunk 255b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk255b : (2555 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk255b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2555 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2555) boundChunk255b⟩)).all (checkFun ⟨2555 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2555) boundChunk255b⟩) = true ∧ linkFun ⟨2555 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2555) boundChunk255b⟩ = true := by
  decide +kernel

end BranchC.A2Check
