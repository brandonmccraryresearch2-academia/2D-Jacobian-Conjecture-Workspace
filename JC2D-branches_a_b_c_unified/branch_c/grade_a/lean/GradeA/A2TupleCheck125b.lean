/- A2 tuple-check chunk 125b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk125b : (1255 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk125b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1255 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1255) boundChunk125b⟩)).all (checkFun ⟨1255 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1255) boundChunk125b⟩) = true ∧ linkFun ⟨1255 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1255) boundChunk125b⟩ = true := by
  decide +kernel

end BranchC.A2Check
