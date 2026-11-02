/- A2 tuple-check chunk 305a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk305a2 : (3052 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk305a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3052 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3052) boundChunk305a2⟩)).all (checkFun ⟨3052 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3052) boundChunk305a2⟩) = true ∧ linkFun ⟨3052 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3052) boundChunk305a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
