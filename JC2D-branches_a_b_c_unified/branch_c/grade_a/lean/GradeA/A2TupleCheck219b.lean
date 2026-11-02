/- A2 tuple-check chunk 219b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk219b : (2195 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk219b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2195 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2195) boundChunk219b⟩)).all (checkFun ⟨2195 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2195) boundChunk219b⟩) = true ∧ linkFun ⟨2195 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2195) boundChunk219b⟩ = true := by
  decide +kernel

end BranchC.A2Check
