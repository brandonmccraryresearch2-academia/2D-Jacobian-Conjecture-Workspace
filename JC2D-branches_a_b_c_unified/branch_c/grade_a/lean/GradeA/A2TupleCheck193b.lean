/- A2 tuple-check chunk 193b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk193b : (1935 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk193b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1935 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1935) boundChunk193b⟩)).all (checkFun ⟨1935 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1935) boundChunk193b⟩) = true ∧ linkFun ⟨1935 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1935) boundChunk193b⟩ = true := by
  decide +kernel

end BranchC.A2Check
