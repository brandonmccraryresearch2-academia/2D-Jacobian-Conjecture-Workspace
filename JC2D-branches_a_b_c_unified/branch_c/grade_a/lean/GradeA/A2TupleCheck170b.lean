/- A2 tuple-check chunk 170b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk170b : (1705 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk170b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1705 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1705) boundChunk170b⟩)).all (checkFun ⟨1705 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1705) boundChunk170b⟩) = true ∧ linkFun ⟨1705 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1705) boundChunk170b⟩ = true := by
  decide +kernel

end BranchC.A2Check
