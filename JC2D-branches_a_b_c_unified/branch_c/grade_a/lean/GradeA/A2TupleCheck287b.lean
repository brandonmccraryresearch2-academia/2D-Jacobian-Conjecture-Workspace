/- A2 tuple-check chunk 287b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk287b : (2875 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk287b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2875 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2875) boundChunk287b⟩)).all (checkFun ⟨2875 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2875) boundChunk287b⟩) = true ∧ linkFun ⟨2875 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2875) boundChunk287b⟩ = true := by
  decide +kernel

end BranchC.A2Check
