/- A2 tuple-check chunk 134a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk134a : (1340 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk134a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1340) boundChunk134a⟩)).all (checkFun ⟨1340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1340) boundChunk134a⟩) = true ∧ linkFun ⟨1340 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1340) boundChunk134a⟩ = true := by
  decide +kernel

end BranchC.A2Check
