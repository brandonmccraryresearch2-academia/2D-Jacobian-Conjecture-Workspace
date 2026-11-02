/- A2 tuple-check chunk 130a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk130a : (1300 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk130a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1300) boundChunk130a⟩)).all (checkFun ⟨1300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1300) boundChunk130a⟩) = true ∧ linkFun ⟨1300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1300) boundChunk130a⟩ = true := by
  decide +kernel

end BranchC.A2Check
