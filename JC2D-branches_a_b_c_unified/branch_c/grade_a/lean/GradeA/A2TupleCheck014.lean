/- A2 tuple-check chunk 14 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk14 : (140 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk14 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 140) boundChunk14⟩)).all (checkFun ⟨140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 140) boundChunk14⟩) = true ∧ linkFun ⟨140 + j, Nat.lt_trans (Nat.add_lt_add_left hj 140) boundChunk14⟩ = true := by
  decide +kernel

end BranchC.A2Check
