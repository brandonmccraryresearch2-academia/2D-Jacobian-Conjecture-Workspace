/- A2 tuple-check chunk 160a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk160a : (1600 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk160a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1600 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1600) boundChunk160a⟩)).all (checkFun ⟨1600 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1600) boundChunk160a⟩) = true ∧ linkFun ⟨1600 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1600) boundChunk160a⟩ = true := by
  decide +kernel

end BranchC.A2Check
