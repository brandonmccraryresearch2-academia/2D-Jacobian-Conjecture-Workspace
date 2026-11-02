import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
theorem probeSum1rt : tupleSumNatT ⟨0, by decide⟩ (0,0,0,0,0) = tupleSumNatT ⟨0, by decide⟩ (0,0,0,0,0) := by decide +kernel
end BranchC.A2Check
