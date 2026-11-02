/- A2 tuple-check chunk 242b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk242b : (2425 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk242b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2425 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2425) boundChunk242b⟩)).all (checkFun ⟨2425 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2425) boundChunk242b⟩) = true ∧ linkFun ⟨2425 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2425) boundChunk242b⟩ = true := by
  decide +kernel

end BranchC.A2Check
