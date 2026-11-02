/- A2 tuple-check chunk 237a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk237a : (2370 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk237a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2370) boundChunk237a⟩)).all (checkFun ⟨2370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2370) boundChunk237a⟩) = true ∧ linkFun ⟨2370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2370) boundChunk237a⟩ = true := by
  decide +kernel

end BranchC.A2Check
