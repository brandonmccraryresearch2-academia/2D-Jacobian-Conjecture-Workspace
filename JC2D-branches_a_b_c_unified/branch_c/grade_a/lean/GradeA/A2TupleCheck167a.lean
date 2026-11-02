/- A2 tuple-check chunk 167a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk167a : (1670 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk167a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1670 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1670) boundChunk167a⟩)).all (checkFun ⟨1670 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1670) boundChunk167a⟩) = true ∧ linkFun ⟨1670 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1670) boundChunk167a⟩ = true := by
  decide +kernel

end BranchC.A2Check
