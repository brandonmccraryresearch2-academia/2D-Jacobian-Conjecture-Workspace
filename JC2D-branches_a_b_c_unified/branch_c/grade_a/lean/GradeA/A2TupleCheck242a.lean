/- A2 tuple-check chunk 242a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk242a : (2420 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk242a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2420) boundChunk242a⟩)).all (checkFun ⟨2420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2420) boundChunk242a⟩) = true ∧ linkFun ⟨2420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2420) boundChunk242a⟩ = true := by
  decide +kernel

end BranchC.A2Check
