/- A2 tuple-check chunk 207a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk207a : (2070 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk207a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2070) boundChunk207a⟩)).all (checkFun ⟨2070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2070) boundChunk207a⟩) = true ∧ linkFun ⟨2070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2070) boundChunk207a⟩ = true := by
  decide +kernel

end BranchC.A2Check
