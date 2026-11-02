import RCCommon
import A1Data
import A1DispatchBase

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A1Test

open BranchC.A1Data

theorem testCol0 : ∀ j : Nat, j < 400 →
    BranchC.RankCheck.colOK (400 * 0 + j) (XSumNat (400 * 0 + j)) = true := by
  decide +kernel

end BranchC.A1Test
