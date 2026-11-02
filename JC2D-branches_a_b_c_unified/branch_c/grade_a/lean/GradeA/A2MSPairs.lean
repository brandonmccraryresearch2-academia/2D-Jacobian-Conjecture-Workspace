/- Pivot-column entries keyed by row tuple (core-only data).
Emitted by grade_a/emit_a2check.py from inv_work_M.pkl.
msTuplePairs c = [(rowTuple, value)] for pivot column c. -/
import GradeA.A2MSPairs00
import GradeA.A2MSPairs01
import GradeA.A2MSPairs02
import GradeA.A2MSPairs03
import GradeA.A2MSPairs04
import GradeA.A2MSPairs05
import GradeA.A2MSPairs06
import GradeA.A2MSPairs07

namespace BranchC.A2MSPairs

def msTuplePairs (c : Nat) : List ((Nat × Nat × Nat × Nat × Nat) × Nat) :=
  if c < 400 then msTuplePairsPart0.getD (c - 0) [] else
  if c < 800 then msTuplePairsPart1.getD (c - 400) [] else
  if c < 1200 then msTuplePairsPart2.getD (c - 800) [] else
  if c < 1600 then msTuplePairsPart3.getD (c - 1200) [] else
  if c < 2000 then msTuplePairsPart4.getD (c - 1600) [] else
  if c < 2400 then msTuplePairsPart5.getD (c - 2000) [] else
  if c < 2800 then msTuplePairsPart6.getD (c - 2400) [] else
  msTuplePairsPart7.getD (c - 2800) []

end BranchC.A2MSPairs
