/- A2 tuple-check chunk 203b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk203b : (2035 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk203b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2035 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2035) boundChunk203b⟩)).all (checkFun ⟨2035 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2035) boundChunk203b⟩) = true ∧ linkFun ⟨2035 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2035) boundChunk203b⟩ = true := by
  decide +kernel

end BranchC.A2Check
