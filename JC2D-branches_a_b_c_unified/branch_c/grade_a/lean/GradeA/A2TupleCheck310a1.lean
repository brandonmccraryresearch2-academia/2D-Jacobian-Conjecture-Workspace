/- A2 tuple-check chunk 310a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk310a1 : (3100 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk310a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3100) boundChunk310a1⟩)).all (checkFun ⟨3100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3100) boundChunk310a1⟩) = true ∧ linkFun ⟨3100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3100) boundChunk310a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
