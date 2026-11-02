/- A2 tuple-check chunk 258a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk258a : (2580 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk258a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2580) boundChunk258a⟩)).all (checkFun ⟨2580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2580) boundChunk258a⟩) = true ∧ linkFun ⟨2580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2580) boundChunk258a⟩ = true := by
  decide +kernel

end BranchC.A2Check
