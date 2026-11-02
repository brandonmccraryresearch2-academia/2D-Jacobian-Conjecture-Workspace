/- A2 tuple-check chunk 253b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk253b : (2535 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk253b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2535 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2535) boundChunk253b⟩)).all (checkFun ⟨2535 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2535) boundChunk253b⟩) = true ∧ linkFun ⟨2535 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2535) boundChunk253b⟩ = true := by
  decide +kernel

end BranchC.A2Check
