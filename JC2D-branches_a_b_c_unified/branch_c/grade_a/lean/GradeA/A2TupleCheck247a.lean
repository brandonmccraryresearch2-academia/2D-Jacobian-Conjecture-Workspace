/- A2 tuple-check chunk 247a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk247a : (2470 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk247a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2470 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2470) boundChunk247a⟩)).all (checkFun ⟨2470 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2470) boundChunk247a⟩) = true ∧ linkFun ⟨2470 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2470) boundChunk247a⟩ = true := by
  decide +kernel

end BranchC.A2Check
