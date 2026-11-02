/- A2 tuple-check chunk 170a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk170a : (1700 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk170a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1700 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1700) boundChunk170a⟩)).all (checkFun ⟨1700 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1700) boundChunk170a⟩) = true ∧ linkFun ⟨1700 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1700) boundChunk170a⟩ = true := by
  decide +kernel

end BranchC.A2Check
