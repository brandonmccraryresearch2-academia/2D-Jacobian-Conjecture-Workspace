/- A2 tuple-check chunk 180a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk180a : (1800 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk180a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1800 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1800) boundChunk180a⟩)).all (checkFun ⟨1800 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1800) boundChunk180a⟩) = true ∧ linkFun ⟨1800 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1800) boundChunk180a⟩ = true := by
  decide +kernel

end BranchC.A2Check
