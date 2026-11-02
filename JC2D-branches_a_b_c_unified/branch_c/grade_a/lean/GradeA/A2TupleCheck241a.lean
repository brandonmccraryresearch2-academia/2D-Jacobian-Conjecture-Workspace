/- A2 tuple-check chunk 241a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk241a : (2410 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk241a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2410) boundChunk241a⟩)).all (checkFun ⟨2410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2410) boundChunk241a⟩) = true ∧ linkFun ⟨2410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2410) boundChunk241a⟩ = true := by
  decide +kernel

end BranchC.A2Check
