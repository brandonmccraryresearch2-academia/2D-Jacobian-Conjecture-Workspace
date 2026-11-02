import RCCommon
import A1Data
import A1DispatchBase

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A1Test

open BranchC.A1Data
open BranchC.A1Inst

theorem testHX100 : ∀ j : Nat, j < 100 →
    ((termsFunNat (400 * 0 + j)).map (fun t => t.1 * t.2)).sum
      = XSumNat (400 * 0 + j) := by
  decide +kernel

end BranchC.A1Test
