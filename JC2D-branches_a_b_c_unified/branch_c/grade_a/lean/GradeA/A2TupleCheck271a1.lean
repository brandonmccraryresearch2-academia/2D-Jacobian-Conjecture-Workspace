/- A2 tuple-check chunk 271a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk271a1 : (2710 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk271a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2710 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2710) boundChunk271a1⟩)).all (checkFun ⟨2710 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2710) boundChunk271a1⟩) = true ∧ linkFun ⟨2710 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2710) boundChunk271a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
