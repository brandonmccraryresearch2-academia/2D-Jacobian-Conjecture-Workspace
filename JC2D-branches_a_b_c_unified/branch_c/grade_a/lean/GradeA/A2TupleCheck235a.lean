/- A2 tuple-check chunk 235a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk235a : (2350 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk235a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2350 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2350) boundChunk235a⟩)).all (checkFun ⟨2350 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2350) boundChunk235a⟩) = true ∧ linkFun ⟨2350 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2350) boundChunk235a⟩ = true := by
  decide +kernel

end BranchC.A2Check
