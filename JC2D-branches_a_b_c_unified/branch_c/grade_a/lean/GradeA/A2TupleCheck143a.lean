/- A2 tuple-check chunk 143a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk143a : (1430 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk143a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1430) boundChunk143a⟩)).all (checkFun ⟨1430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1430) boundChunk143a⟩) = true ∧ linkFun ⟨1430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1430) boundChunk143a⟩ = true := by
  decide +kernel

end BranchC.A2Check
