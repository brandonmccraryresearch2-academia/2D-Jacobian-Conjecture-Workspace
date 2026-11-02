/- A2 tuple-check chunk 16 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk16 : (160 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk16 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 160) boundChunk16⟩)).all (checkFun ⟨160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 160) boundChunk16⟩) = true ∧ linkFun ⟨160 + j, Nat.lt_trans (Nat.add_lt_add_left hj 160) boundChunk16⟩ = true := by
  decide +kernel

end BranchC.A2Check
