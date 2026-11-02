/- A2 tuple-check chunk 5 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk5 : (50 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk5 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨50 + j, Nat.lt_trans (Nat.add_lt_add_left hj 50) boundChunk5⟩)).all (checkFun ⟨50 + j, Nat.lt_trans (Nat.add_lt_add_left hj 50) boundChunk5⟩) = true ∧ linkFun ⟨50 + j, Nat.lt_trans (Nat.add_lt_add_left hj 50) boundChunk5⟩ = true := by
  decide +kernel

end BranchC.A2Check
