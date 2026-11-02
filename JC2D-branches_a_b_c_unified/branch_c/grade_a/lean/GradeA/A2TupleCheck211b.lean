/- A2 tuple-check chunk 211b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk211b : (2115 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk211b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2115 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2115) boundChunk211b⟩)).all (checkFun ⟨2115 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2115) boundChunk211b⟩) = true ∧ linkFun ⟨2115 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2115) boundChunk211b⟩ = true := by
  decide +kernel

end BranchC.A2Check
