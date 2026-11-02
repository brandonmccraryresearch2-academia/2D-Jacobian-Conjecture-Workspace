import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
theorem probeCol0All : (unionTuples ⟨0, by decide⟩).all (checkFun ⟨0, by decide⟩) = true := by decide +kernel
end BranchC.A2Check
