/- Probe: whole-column check as a tail-recursive foldl, no ∀-decide, no List.all.
   List.all is brecOn-based, so this probe avoids it at both levels. -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

/-- Per-column check, foldl form (no List.all). -/
def checkAllFold (c : Fin 3199) : Bool :=
  (unionTuples c).foldl (fun acc rt => acc && checkFun c rt) true

/-- Per-index check, with the out-of-range case trivially true. -/
def checkBool (j : Nat) : Bool :=
  if h : j < 3199 then checkAllFold ⟨j, h⟩ && linkFun ⟨j, h⟩ else true

/-- All 3199 columns, foldl form. -/
def allCheckFold : Bool :=
  (List.range 3199).foldl (fun acc j => acc && checkBool j) true

theorem probeAllFold : allCheckFold = true := by
  decide +kernel

end BranchC.A2Check
