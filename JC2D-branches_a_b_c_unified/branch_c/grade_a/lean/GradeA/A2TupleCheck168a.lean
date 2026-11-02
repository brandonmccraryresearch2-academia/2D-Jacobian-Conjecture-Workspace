/- A2 tuple-check chunk 168a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk168a : (1680 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk168a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1680) boundChunk168a⟩)).all (checkFun ⟨1680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1680) boundChunk168a⟩) = true ∧ linkFun ⟨1680 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1680) boundChunk168a⟩ = true := by
  decide +kernel

end BranchC.A2Check
