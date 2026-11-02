/- A2 tuple-check chunk 81 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk81 : (810 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk81 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨810 + j, Nat.lt_trans (Nat.add_lt_add_left hj 810) boundChunk81⟩)).all (checkFun ⟨810 + j, Nat.lt_trans (Nat.add_lt_add_left hj 810) boundChunk81⟩) = true ∧ linkFun ⟨810 + j, Nat.lt_trans (Nat.add_lt_add_left hj 810) boundChunk81⟩ = true := by
  decide +kernel

end BranchC.A2Check
