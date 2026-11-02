/- A2 tuple-check chunk 274b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk274b : (2745 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk274b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2745 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2745) boundChunk274b⟩)).all (checkFun ⟨2745 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2745) boundChunk274b⟩) = true ∧ linkFun ⟨2745 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2745) boundChunk274b⟩ = true := by
  decide +kernel

end BranchC.A2Check
