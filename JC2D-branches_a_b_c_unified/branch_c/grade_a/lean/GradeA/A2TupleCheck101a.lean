/- A2 tuple-check chunk 101a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk101a : (1010 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk101a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1010 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1010) boundChunk101a⟩)).all (checkFun ⟨1010 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1010) boundChunk101a⟩) = true ∧ linkFun ⟨1010 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1010) boundChunk101a⟩ = true := by
  decide +kernel

end BranchC.A2Check
