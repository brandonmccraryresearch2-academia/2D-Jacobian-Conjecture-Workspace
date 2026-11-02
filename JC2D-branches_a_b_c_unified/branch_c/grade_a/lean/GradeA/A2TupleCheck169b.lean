/- A2 tuple-check chunk 169b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk169b : (1695 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk169b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1695 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1695) boundChunk169b⟩)).all (checkFun ⟨1695 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1695) boundChunk169b⟩) = true ∧ linkFun ⟨1695 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1695) boundChunk169b⟩ = true := by
  decide +kernel

end BranchC.A2Check
