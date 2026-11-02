/- A2 tuple-check chunk 68 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk68 : (680 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk68 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 680) boundChunk68⟩)).all (checkFun ⟨680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 680) boundChunk68⟩) = true ∧ linkFun ⟨680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 680) boundChunk68⟩ = true := by
  decide +kernel

end BranchC.A2Check
