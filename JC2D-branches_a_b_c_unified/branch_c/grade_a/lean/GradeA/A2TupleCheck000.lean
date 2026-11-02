/- A2 tuple-check chunk 0 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk0 : (0 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk0 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨0 + j, Nat.lt_trans (Nat.add_lt_add_left hj 0) boundChunk0⟩)).all (checkFun ⟨0 + j, Nat.lt_trans (Nat.add_lt_add_left hj 0) boundChunk0⟩) = true ∧ linkFun ⟨0 + j, Nat.lt_trans (Nat.add_lt_add_left hj 0) boundChunk0⟩ = true := by
  decide +kernel

end BranchC.A2Check
