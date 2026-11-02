import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
def dedup5 (l : List (Nat × Nat × Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat) :=
  l.foldr (fun x acc => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []
theorem probeCol0Dedup : (dedup5 (unionTuples ⟨0, by decide⟩)).all (checkFun ⟨0, by decide⟩) = true := by decide +kernel
end BranchC.A2Check
