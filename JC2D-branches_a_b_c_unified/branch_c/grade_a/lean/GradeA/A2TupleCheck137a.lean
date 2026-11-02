/- A2 tuple-check chunk 137a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk137a : (1370 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk137a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1370) boundChunk137a⟩)).all (checkFun ⟨1370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1370) boundChunk137a⟩) = true ∧ linkFun ⟨1370 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1370) boundChunk137a⟩ = true := by
  decide +kernel

end BranchC.A2Check
