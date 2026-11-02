/- A2 tuple-check chunk 199a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk199a : (1990 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk199a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1990) boundChunk199a⟩)).all (checkFun ⟨1990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1990) boundChunk199a⟩) = true ∧ linkFun ⟨1990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1990) boundChunk199a⟩ = true := by
  decide +kernel

end BranchC.A2Check
