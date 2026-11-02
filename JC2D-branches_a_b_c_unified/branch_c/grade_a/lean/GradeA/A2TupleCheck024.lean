/- A2 tuple-check chunk 24 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk24 : (240 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk24 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨240 + j, Nat.lt_trans (Nat.add_lt_add_left hj 240) boundChunk24⟩)).all (checkFun ⟨240 + j, Nat.lt_trans (Nat.add_lt_add_left hj 240) boundChunk24⟩) = true ∧ linkFun ⟨240 + j, Nat.lt_trans (Nat.add_lt_add_left hj 240) boundChunk24⟩ = true := by
  decide +kernel

end BranchC.A2Check
