/- A2 tuple-check chunk 89 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk89 : (890 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk89 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 890) boundChunk89⟩)).all (checkFun ⟨890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 890) boundChunk89⟩) = true ∧ linkFun ⟨890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 890) boundChunk89⟩ = true := by
  decide +kernel

end BranchC.A2Check
