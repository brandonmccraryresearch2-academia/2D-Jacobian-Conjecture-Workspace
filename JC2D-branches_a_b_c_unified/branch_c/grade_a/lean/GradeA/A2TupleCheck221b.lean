/- A2 tuple-check chunk 221b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk221b : (2215 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk221b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2215 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2215) boundChunk221b⟩)).all (checkFun ⟨2215 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2215) boundChunk221b⟩) = true ∧ linkFun ⟨2215 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2215) boundChunk221b⟩ = true := by
  decide +kernel

end BranchC.A2Check
