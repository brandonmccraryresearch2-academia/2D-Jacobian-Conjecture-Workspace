/- A2 tuple-check chunk 310b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk310b1 : (3105 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk310b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3105 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3105) boundChunk310b1⟩)).all (checkFun ⟨3105 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3105) boundChunk310b1⟩) = true ∧ linkFun ⟨3105 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3105) boundChunk310b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
