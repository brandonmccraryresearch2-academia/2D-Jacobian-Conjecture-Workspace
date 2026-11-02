import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
theorem probeCheck1rt : checkFun ⟨0, by decide⟩ (0,0,0,0,0) = true := by decide +kernel
end BranchC.A2Check
