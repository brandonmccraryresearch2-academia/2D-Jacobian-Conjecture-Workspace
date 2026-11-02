/- A2 tuple-check chunk 193a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk193a : (1930 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk193a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1930) boundChunk193a⟩)).all (checkFun ⟨1930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1930) boundChunk193a⟩) = true ∧ linkFun ⟨1930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1930) boundChunk193a⟩ = true := by
  decide +kernel

end BranchC.A2Check
