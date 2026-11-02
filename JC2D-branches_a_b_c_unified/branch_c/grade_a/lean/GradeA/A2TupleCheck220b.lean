/- A2 tuple-check chunk 220b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk220b : (2205 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk220b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2205 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2205) boundChunk220b⟩)).all (checkFun ⟨2205 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2205) boundChunk220b⟩) = true ∧ linkFun ⟨2205 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2205) boundChunk220b⟩ = true := by
  decide +kernel

end BranchC.A2Check
