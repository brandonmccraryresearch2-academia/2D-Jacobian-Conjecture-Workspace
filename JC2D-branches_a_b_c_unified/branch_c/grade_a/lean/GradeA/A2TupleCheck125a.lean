/- A2 tuple-check chunk 125a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk125a : (1250 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk125a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1250) boundChunk125a⟩)).all (checkFun ⟨1250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1250) boundChunk125a⟩) = true ∧ linkFun ⟨1250 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1250) boundChunk125a⟩ = true := by
  decide +kernel

end BranchC.A2Check
