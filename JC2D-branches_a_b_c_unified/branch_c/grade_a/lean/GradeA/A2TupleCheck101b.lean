/- A2 tuple-check chunk 101b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk101b : (1015 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk101b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1015 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1015) boundChunk101b⟩)).all (checkFun ⟨1015 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1015) boundChunk101b⟩) = true ∧ linkFun ⟨1015 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1015) boundChunk101b⟩ = true := by
  decide +kernel

end BranchC.A2Check
