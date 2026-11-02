/- A2 tuple-check chunk 2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk2 : (20 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk2 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨20 + j, Nat.lt_trans (Nat.add_lt_add_left hj 20) boundChunk2⟩)).all (checkFun ⟨20 + j, Nat.lt_trans (Nat.add_lt_add_left hj 20) boundChunk2⟩) = true ∧ linkFun ⟨20 + j, Nat.lt_trans (Nat.add_lt_add_left hj 20) boundChunk2⟩ = true := by
  decide +kernel

end BranchC.A2Check
