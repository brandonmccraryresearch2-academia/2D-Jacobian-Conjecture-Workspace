/- A2 tuple-check chunk 268a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk268a1 : (2680 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk268a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2680) boundChunk268a1⟩)).all (checkFun ⟨2680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2680) boundChunk268a1⟩) = true ∧ linkFun ⟨2680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2680) boundChunk268a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
