/- A2 tuple-check chunk 57 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk57 : (570 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk57 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 570) boundChunk57⟩)).all (checkFun ⟨570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 570) boundChunk57⟩) = true ∧ linkFun ⟨570 + j, Nat.lt_trans (Nat.add_lt_add_left hj 570) boundChunk57⟩ = true := by
  decide +kernel

end BranchC.A2Check
