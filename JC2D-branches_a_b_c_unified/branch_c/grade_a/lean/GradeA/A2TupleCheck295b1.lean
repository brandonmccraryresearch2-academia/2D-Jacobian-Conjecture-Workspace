/- A2 tuple-check chunk 295b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk295b1 : (2955 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk295b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2955 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2955) boundChunk295b1⟩)).all (checkFun ⟨2955 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2955) boundChunk295b1⟩) = true ∧ linkFun ⟨2955 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2955) boundChunk295b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
