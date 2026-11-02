/- A2 tuple-check chunk 230a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk230a : (2300 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk230a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2300) boundChunk230a⟩)).all (checkFun ⟨2300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2300) boundChunk230a⟩) = true ∧ linkFun ⟨2300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2300) boundChunk230a⟩ = true := by
  decide +kernel

end BranchC.A2Check
