/- A2 tuple-check chunk 55 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk55 : (550 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk55 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨550 + j, Nat.lt_trans (Nat.add_lt_add_left hj 550) boundChunk55⟩)).all (checkFun ⟨550 + j, Nat.lt_trans (Nat.add_lt_add_left hj 550) boundChunk55⟩) = true ∧ linkFun ⟨550 + j, Nat.lt_trans (Nat.add_lt_add_left hj 550) boundChunk55⟩ = true := by
  decide +kernel

end BranchC.A2Check
