/- A2 tuple-check chunk 300b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk300b1 : (3005 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk300b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3005 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3005) boundChunk300b1⟩)).all (checkFun ⟨3005 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3005) boundChunk300b1⟩) = true ∧ linkFun ⟨3005 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3005) boundChunk300b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
