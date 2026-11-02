/- A2 tuple-check chunk 228a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk228a : (2280 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk228a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2280) boundChunk228a⟩)).all (checkFun ⟨2280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2280) boundChunk228a⟩) = true ∧ linkFun ⟨2280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2280) boundChunk228a⟩ = true := by
  decide +kernel

end BranchC.A2Check
