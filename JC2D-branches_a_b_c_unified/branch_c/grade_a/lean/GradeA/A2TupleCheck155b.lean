/- A2 tuple-check chunk 155b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk155b : (1555 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk155b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1555 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1555) boundChunk155b⟩)).all (checkFun ⟨1555 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1555) boundChunk155b⟩) = true ∧ linkFun ⟨1555 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1555) boundChunk155b⟩ = true := by
  decide +kernel

end BranchC.A2Check
