/- A2 tuple-check chunk 161a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk161a : (1610 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk161a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1610) boundChunk161a⟩)).all (checkFun ⟨1610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1610) boundChunk161a⟩) = true ∧ linkFun ⟨1610 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1610) boundChunk161a⟩ = true := by
  decide +kernel

end BranchC.A2Check
