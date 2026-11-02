/- A2 tuple-check chunk 95 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk95 : (950 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk95 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨950 + j, Nat.lt_trans (Nat.add_lt_add_left hj 950) boundChunk95⟩)).all (checkFun ⟨950 + j, Nat.lt_trans (Nat.add_lt_add_left hj 950) boundChunk95⟩) = true ∧ linkFun ⟨950 + j, Nat.lt_trans (Nat.add_lt_add_left hj 950) boundChunk95⟩ = true := by
  decide +kernel

end BranchC.A2Check
