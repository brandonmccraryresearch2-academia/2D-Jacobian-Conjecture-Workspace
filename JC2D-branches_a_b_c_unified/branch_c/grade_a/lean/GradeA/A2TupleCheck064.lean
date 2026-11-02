/- A2 tuple-check chunk 64 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk64 : (640 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk64 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨640 + j, Nat.lt_trans (Nat.add_lt_add_left hj 640) boundChunk64⟩)).all (checkFun ⟨640 + j, Nat.lt_trans (Nat.add_lt_add_left hj 640) boundChunk64⟩) = true ∧ linkFun ⟨640 + j, Nat.lt_trans (Nat.add_lt_add_left hj 640) boundChunk64⟩ = true := by
  decide +kernel

end BranchC.A2Check
