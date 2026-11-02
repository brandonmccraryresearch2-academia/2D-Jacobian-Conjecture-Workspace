/- A2 tuple-check chunk 179a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk179a : (1790 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk179a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1790) boundChunk179a⟩)).all (checkFun ⟨1790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1790) boundChunk179a⟩) = true ∧ linkFun ⟨1790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1790) boundChunk179a⟩ = true := by
  decide +kernel

end BranchC.A2Check
