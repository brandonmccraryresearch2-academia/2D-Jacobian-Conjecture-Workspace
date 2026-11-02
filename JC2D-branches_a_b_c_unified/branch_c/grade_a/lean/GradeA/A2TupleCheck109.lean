/- A2 tuple-check chunk 109 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk109 : (1090 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk109 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1090 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1090) boundChunk109⟩)).all (checkFun ⟨1090 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1090) boundChunk109⟩) = true ∧ linkFun ⟨1090 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1090) boundChunk109⟩ = true := by
  decide +kernel

end BranchC.A2Check
