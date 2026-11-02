import RCCommon
import MaskLemma

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000

example {x : Nat} (h : BranchC.RankCheck.slotOK x = true) :
    BranchC.Mask.slotOK x = true := h

example {j X : Nat} (h : BranchC.RankCheck.colOK j X = true) :
    BranchC.Mask.colOK j X = true := h
