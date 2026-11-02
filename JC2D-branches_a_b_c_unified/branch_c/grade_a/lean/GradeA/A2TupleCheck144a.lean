/- A2 tuple-check chunk 144a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk144a : (1440 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk144a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1440) boundChunk144a⟩)).all (checkFun ⟨1440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1440) boundChunk144a⟩) = true ∧ linkFun ⟨1440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1440) boundChunk144a⟩ = true := by
  decide +kernel

end BranchC.A2Check
