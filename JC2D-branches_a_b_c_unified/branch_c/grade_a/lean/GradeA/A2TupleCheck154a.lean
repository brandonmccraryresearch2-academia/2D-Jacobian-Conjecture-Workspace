/- A2 tuple-check chunk 154a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk154a : (1540 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk154a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1540) boundChunk154a⟩)).all (checkFun ⟨1540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1540) boundChunk154a⟩) = true ∧ linkFun ⟨1540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1540) boundChunk154a⟩ = true := by
  decide +kernel

end BranchC.A2Check
