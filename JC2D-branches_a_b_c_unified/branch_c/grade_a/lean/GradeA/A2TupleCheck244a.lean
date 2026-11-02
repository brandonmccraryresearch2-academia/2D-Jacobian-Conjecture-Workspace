/- A2 tuple-check chunk 244a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk244a : (2440 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk244a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2440) boundChunk244a⟩)).all (checkFun ⟨2440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2440) boundChunk244a⟩) = true ∧ linkFun ⟨2440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2440) boundChunk244a⟩ = true := by
  decide +kernel

end BranchC.A2Check
