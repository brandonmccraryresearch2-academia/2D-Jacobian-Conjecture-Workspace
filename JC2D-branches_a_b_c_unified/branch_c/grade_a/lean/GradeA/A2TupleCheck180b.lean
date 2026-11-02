/- A2 tuple-check chunk 180b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk180b : (1805 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk180b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1805 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1805) boundChunk180b⟩)).all (checkFun ⟨1805 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1805) boundChunk180b⟩) = true ∧ linkFun ⟨1805 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1805) boundChunk180b⟩ = true := by
  decide +kernel

end BranchC.A2Check
