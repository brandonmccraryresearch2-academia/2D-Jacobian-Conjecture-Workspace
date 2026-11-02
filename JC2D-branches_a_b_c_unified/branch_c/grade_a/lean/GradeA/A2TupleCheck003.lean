/- A2 tuple-check chunk 3 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk3 : (30 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk3 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨30 + j, Nat.lt_trans (Nat.add_lt_add_left hj 30) boundChunk3⟩)).all (checkFun ⟨30 + j, Nat.lt_trans (Nat.add_lt_add_left hj 30) boundChunk3⟩) = true ∧ linkFun ⟨30 + j, Nat.lt_trans (Nat.add_lt_add_left hj 30) boundChunk3⟩ = true := by
  decide +kernel

end BranchC.A2Check
