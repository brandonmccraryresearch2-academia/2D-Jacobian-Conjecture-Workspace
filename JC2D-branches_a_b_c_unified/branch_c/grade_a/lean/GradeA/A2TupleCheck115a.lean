/- A2 tuple-check chunk 115a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk115a : (1150 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk115a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1150 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1150) boundChunk115a⟩)).all (checkFun ⟨1150 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1150) boundChunk115a⟩) = true ∧ linkFun ⟨1150 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1150) boundChunk115a⟩ = true := by
  decide +kernel

end BranchC.A2Check
