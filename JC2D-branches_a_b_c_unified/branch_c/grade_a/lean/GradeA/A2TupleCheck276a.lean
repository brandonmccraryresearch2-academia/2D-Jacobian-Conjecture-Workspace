/- A2 tuple-check chunk 276a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk276a : (2760 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk276a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2760) boundChunk276a⟩)).all (checkFun ⟨2760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2760) boundChunk276a⟩) = true ∧ linkFun ⟨2760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2760) boundChunk276a⟩ = true := by
  decide +kernel

end BranchC.A2Check
