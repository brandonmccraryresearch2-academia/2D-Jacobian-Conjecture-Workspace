/- A2 tuple-check chunk 87 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk87 : (870 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk87 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨870 + j, Nat.lt_trans (Nat.add_lt_add_left hj 870) boundChunk87⟩)).all (checkFun ⟨870 + j, Nat.lt_trans (Nat.add_lt_add_left hj 870) boundChunk87⟩) = true ∧ linkFun ⟨870 + j, Nat.lt_trans (Nat.add_lt_add_left hj 870) boundChunk87⟩ = true := by
  decide +kernel

end BranchC.A2Check
