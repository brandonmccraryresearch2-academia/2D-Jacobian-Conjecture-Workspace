/- A2 tuple-check chunk 225a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk225a : (2250 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk225a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2250) boundChunk225a⟩)).all (checkFun ⟨2250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2250) boundChunk225a⟩) = true ∧ linkFun ⟨2250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2250) boundChunk225a⟩ = true := by
  decide +kernel

end BranchC.A2Check
