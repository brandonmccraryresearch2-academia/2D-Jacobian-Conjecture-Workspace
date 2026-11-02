/- A2 tuple-check chunk 4 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk4 : (40 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk4 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨40 + j, Nat.lt_trans (Nat.add_lt_add_left hj 40) boundChunk4⟩)).all (checkFun ⟨40 + j, Nat.lt_trans (Nat.add_lt_add_left hj 40) boundChunk4⟩) = true ∧ linkFun ⟨40 + j, Nat.lt_trans (Nat.add_lt_add_left hj 40) boundChunk4⟩ = true := by
  decide +kernel

end BranchC.A2Check
