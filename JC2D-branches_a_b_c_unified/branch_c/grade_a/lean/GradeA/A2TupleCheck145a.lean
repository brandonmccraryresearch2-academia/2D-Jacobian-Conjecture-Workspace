/- A2 tuple-check chunk 145a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk145a : (1450 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk145a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1450) boundChunk145a⟩)).all (checkFun ⟨1450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1450) boundChunk145a⟩) = true ∧ linkFun ⟨1450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1450) boundChunk145a⟩ = true := by
  decide +kernel

end BranchC.A2Check
