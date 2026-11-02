/- A2 tuple-check chunk 162a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk162a : (1620 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk162a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1620 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1620) boundChunk162a⟩)).all (checkFun ⟨1620 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1620) boundChunk162a⟩) = true ∧ linkFun ⟨1620 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1620) boundChunk162a⟩ = true := by
  decide +kernel

end BranchC.A2Check
