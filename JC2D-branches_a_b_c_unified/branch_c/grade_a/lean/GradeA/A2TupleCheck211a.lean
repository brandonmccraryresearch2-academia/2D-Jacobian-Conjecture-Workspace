/- A2 tuple-check chunk 211a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk211a : (2110 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk211a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2110) boundChunk211a⟩)).all (checkFun ⟨2110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2110) boundChunk211a⟩) = true ∧ linkFun ⟨2110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2110) boundChunk211a⟩ = true := by
  decide +kernel

end BranchC.A2Check
