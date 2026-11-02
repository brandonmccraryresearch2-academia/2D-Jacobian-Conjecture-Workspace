/- A2 tuple-check chunk 224a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk224a : (2240 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk224a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2240 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2240) boundChunk224a⟩)).all (checkFun ⟨2240 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2240) boundChunk224a⟩) = true ∧ linkFun ⟨2240 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2240) boundChunk224a⟩ = true := by
  decide +kernel

end BranchC.A2Check
