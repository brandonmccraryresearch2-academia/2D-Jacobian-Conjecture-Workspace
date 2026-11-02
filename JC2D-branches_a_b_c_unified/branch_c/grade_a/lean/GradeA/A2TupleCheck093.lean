/- A2 tuple-check chunk 93 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk93 : (930 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk93 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 930) boundChunk93⟩)).all (checkFun ⟨930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 930) boundChunk93⟩) = true ∧ linkFun ⟨930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 930) boundChunk93⟩ = true := by
  decide +kernel

end BranchC.A2Check
