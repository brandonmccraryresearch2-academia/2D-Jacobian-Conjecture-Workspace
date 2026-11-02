/- A2 tuple-check chunk 272b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk272b2 : (2727 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk272b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2727 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2727) boundChunk272b2⟩)).all (checkFun ⟨2727 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2727) boundChunk272b2⟩) = true ∧ linkFun ⟨2727 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2727) boundChunk272b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
