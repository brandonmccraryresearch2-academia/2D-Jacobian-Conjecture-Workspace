/- A2 tuple-check chunk 238a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk238a : (2380 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk238a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2380) boundChunk238a⟩)).all (checkFun ⟨2380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2380) boundChunk238a⟩) = true ∧ linkFun ⟨2380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2380) boundChunk238a⟩ = true := by
  decide +kernel

end BranchC.A2Check
