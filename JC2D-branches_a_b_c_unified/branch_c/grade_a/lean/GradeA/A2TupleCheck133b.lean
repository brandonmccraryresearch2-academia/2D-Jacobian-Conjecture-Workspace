/- A2 tuple-check chunk 133b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk133b : (1335 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk133b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1335 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1335) boundChunk133b⟩)).all (checkFun ⟨1335 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1335) boundChunk133b⟩) = true ∧ linkFun ⟨1335 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1335) boundChunk133b⟩ = true := by
  decide +kernel

end BranchC.A2Check
