/- A2 tuple-check chunk 106 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk106 : (1060 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk106 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1060 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1060) boundChunk106⟩)).all (checkFun ⟨1060 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1060) boundChunk106⟩) = true ∧ linkFun ⟨1060 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1060) boundChunk106⟩ = true := by
  decide +kernel

end BranchC.A2Check
