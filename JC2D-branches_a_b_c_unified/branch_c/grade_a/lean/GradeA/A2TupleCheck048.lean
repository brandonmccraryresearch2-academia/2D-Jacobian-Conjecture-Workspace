/- A2 tuple-check chunk 48 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk48 : (480 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk48 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨480 + j, Nat.lt_trans (Nat.add_lt_add_left hj 480) boundChunk48⟩)).all (checkFun ⟨480 + j, Nat.lt_trans (Nat.add_lt_add_left hj 480) boundChunk48⟩) = true ∧ linkFun ⟨480 + j, Nat.lt_trans (Nat.add_lt_add_left hj 480) boundChunk48⟩ = true := by
  decide +kernel

end BranchC.A2Check
