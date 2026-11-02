/- A2 tuple-check chunk 84 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk84 : (840 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk84 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨840 + j, Nat.lt_trans (Nat.add_lt_add_left hj 840) boundChunk84⟩)).all (checkFun ⟨840 + j, Nat.lt_trans (Nat.add_lt_add_left hj 840) boundChunk84⟩) = true ∧ linkFun ⟨840 + j, Nat.lt_trans (Nat.add_lt_add_left hj 840) boundChunk84⟩ = true := by
  decide +kernel

end BranchC.A2Check
