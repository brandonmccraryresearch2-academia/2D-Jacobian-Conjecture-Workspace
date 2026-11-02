/- A2 tuple-check chunk 259a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk259a : (2590 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk259a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2590) boundChunk259a⟩)).all (checkFun ⟨2590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2590) boundChunk259a⟩) = true ∧ linkFun ⟨2590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2590) boundChunk259a⟩ = true := by
  decide +kernel

end BranchC.A2Check
