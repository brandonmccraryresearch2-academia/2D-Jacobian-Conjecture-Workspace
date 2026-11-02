/- A2 tuple-check chunk 77 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk77 : (770 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk77 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨770 + j, Nat.lt_trans (Nat.add_lt_add_left hj 770) boundChunk77⟩)).all (checkFun ⟨770 + j, Nat.lt_trans (Nat.add_lt_add_left hj 770) boundChunk77⟩) = true ∧ linkFun ⟨770 + j, Nat.lt_trans (Nat.add_lt_add_left hj 770) boundChunk77⟩ = true := by
  decide +kernel

end BranchC.A2Check
