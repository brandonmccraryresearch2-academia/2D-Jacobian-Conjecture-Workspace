/- A2 tuple-check chunk 274a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk274a : (2740 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk274a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2740) boundChunk274a⟩)).all (checkFun ⟨2740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2740) boundChunk274a⟩) = true ∧ linkFun ⟨2740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2740) boundChunk274a⟩ = true := by
  decide +kernel

end BranchC.A2Check
