/- A2 tuple-check chunk 210a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk210a : (2100 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk210a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2100) boundChunk210a⟩)).all (checkFun ⟨2100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2100) boundChunk210a⟩) = true ∧ linkFun ⟨2100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2100) boundChunk210a⟩ = true := by
  decide +kernel

end BranchC.A2Check
