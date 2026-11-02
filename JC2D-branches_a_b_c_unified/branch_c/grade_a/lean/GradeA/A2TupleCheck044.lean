/- A2 tuple-check chunk 44 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk44 : (440 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk44 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 440) boundChunk44⟩)).all (checkFun ⟨440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 440) boundChunk44⟩) = true ∧ linkFun ⟨440 + j, Nat.lt_trans (Nat.add_lt_add_left hj 440) boundChunk44⟩ = true := by
  decide +kernel

end BranchC.A2Check
