/- A2 tuple-check chunk 37 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk37 : (370 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk37 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 370) boundChunk37⟩)).all (checkFun ⟨370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 370) boundChunk37⟩) = true ∧ linkFun ⟨370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 370) boundChunk37⟩ = true := by
  decide +kernel

end BranchC.A2Check
