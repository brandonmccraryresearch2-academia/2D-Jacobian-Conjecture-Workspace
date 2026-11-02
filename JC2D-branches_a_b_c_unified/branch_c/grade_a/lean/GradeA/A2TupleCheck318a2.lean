/- A2 tuple-check chunk 318a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk318a2 : (3182 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk318a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3182 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3182) boundChunk318a2⟩)).all (checkFun ⟨3182 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3182) boundChunk318a2⟩) = true ∧ linkFun ⟨3182 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3182) boundChunk318a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
