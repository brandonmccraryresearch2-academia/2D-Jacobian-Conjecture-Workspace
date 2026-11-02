/- A2 tuple-check chunk 214a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk214a : (2140 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk214a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2140) boundChunk214a⟩)).all (checkFun ⟨2140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2140) boundChunk214a⟩) = true ∧ linkFun ⟨2140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2140) boundChunk214a⟩ = true := by
  decide +kernel

end BranchC.A2Check
