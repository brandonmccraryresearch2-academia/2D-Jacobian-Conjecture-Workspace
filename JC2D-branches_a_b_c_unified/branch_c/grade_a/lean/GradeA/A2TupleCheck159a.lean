/- A2 tuple-check chunk 159a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk159a : (1590 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk159a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1590) boundChunk159a⟩)).all (checkFun ⟨1590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1590) boundChunk159a⟩) = true ∧ linkFun ⟨1590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1590) boundChunk159a⟩ = true := by
  decide +kernel

end BranchC.A2Check
