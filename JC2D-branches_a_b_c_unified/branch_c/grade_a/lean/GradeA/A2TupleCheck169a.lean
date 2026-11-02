/- A2 tuple-check chunk 169a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk169a : (1690 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk169a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1690 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1690) boundChunk169a⟩)).all (checkFun ⟨1690 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1690) boundChunk169a⟩) = true ∧ linkFun ⟨1690 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1690) boundChunk169a⟩ = true := by
  decide +kernel

end BranchC.A2Check
