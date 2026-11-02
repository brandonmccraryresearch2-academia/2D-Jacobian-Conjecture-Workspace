/- A2 tuple-check chunk 262a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk262a : (2620 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk262a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2620 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2620) boundChunk262a⟩)).all (checkFun ⟨2620 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2620) boundChunk262a⟩) = true ∧ linkFun ⟨2620 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2620) boundChunk262a⟩ = true := by
  decide +kernel

end BranchC.A2Check
