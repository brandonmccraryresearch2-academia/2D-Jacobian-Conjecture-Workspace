/- A2 tuple-check chunk 35 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk35 : (350 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk35 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨350 + j, Nat.lt_trans (Nat.add_lt_add_left hj 350) boundChunk35⟩)).all (checkFun ⟨350 + j, Nat.lt_trans (Nat.add_lt_add_left hj 350) boundChunk35⟩) = true ∧ linkFun ⟨350 + j, Nat.lt_trans (Nat.add_lt_add_left hj 350) boundChunk35⟩ = true := by
  decide +kernel

end BranchC.A2Check
