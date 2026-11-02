/- A2 tuple-check chunk 234a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk234a : (2340 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk234a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2340) boundChunk234a⟩)).all (checkFun ⟨2340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2340) boundChunk234a⟩) = true ∧ linkFun ⟨2340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2340) boundChunk234a⟩ = true := by
  decide +kernel

end BranchC.A2Check
