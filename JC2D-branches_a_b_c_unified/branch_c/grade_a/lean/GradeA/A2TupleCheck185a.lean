/- A2 tuple-check chunk 185a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk185a : (1850 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk185a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1850) boundChunk185a⟩)).all (checkFun ⟨1850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1850) boundChunk185a⟩) = true ∧ linkFun ⟨1850 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1850) boundChunk185a⟩ = true := by
  decide +kernel

end BranchC.A2Check
