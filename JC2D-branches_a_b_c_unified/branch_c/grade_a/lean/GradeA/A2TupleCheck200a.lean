/- A2 tuple-check chunk 200a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk200a : (2000 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk200a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2000 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2000) boundChunk200a⟩)).all (checkFun ⟨2000 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2000) boundChunk200a⟩) = true ∧ linkFun ⟨2000 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2000) boundChunk200a⟩ = true := by
  decide +kernel

end BranchC.A2Check
