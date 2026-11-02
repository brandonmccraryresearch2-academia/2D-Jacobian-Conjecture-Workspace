/- A2 tuple-check chunk 96 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk96 : (960 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk96 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨960 + j, Nat.lt_trans (Nat.add_lt_add_left hj 960) boundChunk96⟩)).all (checkFun ⟨960 + j, Nat.lt_trans (Nat.add_lt_add_left hj 960) boundChunk96⟩) = true ∧ linkFun ⟨960 + j, Nat.lt_trans (Nat.add_lt_add_left hj 960) boundChunk96⟩ = true := by
  decide +kernel

end BranchC.A2Check
