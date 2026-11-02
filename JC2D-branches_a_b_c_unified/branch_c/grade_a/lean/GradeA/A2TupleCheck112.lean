/- A2 tuple-check chunk 112 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk112 : (1120 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk112 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1120) boundChunk112⟩)).all (checkFun ⟨1120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1120) boundChunk112⟩) = true ∧ linkFun ⟨1120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1120) boundChunk112⟩ = true := by
  decide +kernel

end BranchC.A2Check
