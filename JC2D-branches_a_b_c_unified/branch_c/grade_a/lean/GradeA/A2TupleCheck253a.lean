/- A2 tuple-check chunk 253a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk253a : (2530 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk253a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2530) boundChunk253a⟩)).all (checkFun ⟨2530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2530) boundChunk253a⟩) = true ∧ linkFun ⟨2530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2530) boundChunk253a⟩ = true := by
  decide +kernel

end BranchC.A2Check
