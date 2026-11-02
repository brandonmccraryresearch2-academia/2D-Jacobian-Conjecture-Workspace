/- A2 tuple-check chunk 25 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk25 : (250 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk25 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 250) boundChunk25⟩)).all (checkFun ⟨250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 250) boundChunk25⟩) = true ∧ linkFun ⟨250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 250) boundChunk25⟩ = true := by
  decide +kernel

end BranchC.A2Check
