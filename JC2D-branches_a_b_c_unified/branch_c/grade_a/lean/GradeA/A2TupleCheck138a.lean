/- A2 tuple-check chunk 138a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk138a : (1380 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk138a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1380) boundChunk138a⟩)).all (checkFun ⟨1380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1380) boundChunk138a⟩) = true ∧ linkFun ⟨1380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1380) boundChunk138a⟩ = true := by
  decide +kernel

end BranchC.A2Check
