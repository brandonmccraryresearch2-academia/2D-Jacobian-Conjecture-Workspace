/- A2 tuple-check chunk 196a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk196a : (1960 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk196a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1960 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1960) boundChunk196a⟩)).all (checkFun ⟨1960 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1960) boundChunk196a⟩) = true ∧ linkFun ⟨1960 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1960) boundChunk196a⟩ = true := by
  decide +kernel

end BranchC.A2Check
