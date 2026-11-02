/- A2 tuple-check chunk 85 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk85 : (850 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk85 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 850) boundChunk85⟩)).all (checkFun ⟨850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 850) boundChunk85⟩) = true ∧ linkFun ⟨850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 850) boundChunk85⟩ = true := by
  decide +kernel

end BranchC.A2Check
