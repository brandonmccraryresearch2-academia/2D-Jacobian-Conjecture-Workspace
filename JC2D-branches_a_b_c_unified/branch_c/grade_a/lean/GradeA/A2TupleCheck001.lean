/- A2 tuple-check chunk 1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk1 : (10 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk1 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨10 + j, Nat.lt_trans (Nat.add_lt_add_left hj 10) boundChunk1⟩)).all (checkFun ⟨10 + j, Nat.lt_trans (Nat.add_lt_add_left hj 10) boundChunk1⟩) = true ∧ linkFun ⟨10 + j, Nat.lt_trans (Nat.add_lt_add_left hj 10) boundChunk1⟩ = true := by
  decide +kernel

end BranchC.A2Check
