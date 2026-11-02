/- A2 tuple-check chunk 273a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk273a : (2730 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk273a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2730) boundChunk273a⟩)).all (checkFun ⟨2730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2730) boundChunk273a⟩) = true ∧ linkFun ⟨2730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2730) boundChunk273a⟩ = true := by
  decide +kernel

end BranchC.A2Check
