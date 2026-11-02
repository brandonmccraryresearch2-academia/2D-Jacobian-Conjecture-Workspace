"""emit_a2data.py -- emit the A2 concrete data as Lean (core-only, no Mathlib).

Reads rank_lemma_check/inv_work_M.pkl (rows, cols) and INVERSE.pkl
(piv, pivcols), asserts the pivot structure, and writes
grade_a/lean/GradeA/A2Data.lean:
  rowsList : List (Nat x Nat x Nat x Nat x Nat)   -- M's 3199 rows, in order
  rowTuple : Fin 3199 -> 5-tuple                  -- via getD
  genList  : List (Fin 6)                          -- pivot columns' generators
  genFun   : Fin 3199 -> Fin 6
  multList : List (5-tuple)                        -- pivot columns' multipliers
  multTuple: Fin 3199 -> 5-tuple
  scaleList: List Nat                              -- c_n, as Nats (cast at use site)
  scaleFun : Fin 6 -> Nat

Scale values are the ones derived and verified monomial-wise by
grade_a/a2_numerical_check.py (log grade_a/logs/a2_numerical.log):
  Psi 17276, Phi1 19847, Phi2 22078, Theta1 13509, Theta2 15117, Theta3 29273
in Fpoly order 0=Psi, 1=Phi1, 2=Phi2, 3=Theta1, 4=Theta2, 5=Theta3
(comparator/Challenge.lean Fpoly).  MS itself is NOT re-emitted here:
it is A1Data.colDataNat (grade_a/lean/GradeA/A2's column data source).

The 5-tuples are the fast kernel form for A2's column checks: the generic
entry lemma bridges them to Fin 5 ->0 N monomials (Term.mono / rowMono),
so per-column decides run on plain Nat tuples, not Finsupp arithmetic.
"""
import pickle, os

BC = os.path.expanduser(
    "~/workspace/research/2D-Jacobian-Conjecture-Workspace/"
    "JC2D-branches_a_b_c_unified/branch_c")
GENIDX = {"Psi": 0, "Phi1": 1, "Phi2": 2, "Theta1": 3, "Theta2": 4, "Theta3": 5}
SCALE = [17276, 19847, 22078, 13509, 15117, 29273]  # verified by a2_numerical_check.py

M = pickle.load(open(os.path.join(BC, "rank_lemma_check/inv_work_M.pkl"), "rb"))
I = pickle.load(open(os.path.join(BC, "rank_lemma_check/INVERSE.pkl"), "rb"))
rows, cols, piv, pivcols = M["rows"], M["cols"], I["piv"], I["pivcols"]
assert len(rows) == len(pivcols) == 3199
assert all(cols[j] == pivcols[jj] for jj, j in enumerate(piv))
assert all(len(r) == 5 for r in rows)
assert all(len(m) == 5 for _, m in pivcols)

def tup(t):
    return "(" + ", ".join(map(str, t)) + ")"

lines = []
lines.append("/-")
lines.append("A2 concrete data (branch (c), p = 32003, w0 = 11147).")
lines.append("Emitted by grade_a/emit_a2data.py from rank_lemma_check/inv_work_M.pkl")
lines.append("and INVERSE.pkl (asserted: 3199 rows, 3199 pivot columns, pivcols match).")
lines.append("Scale values verified monomial-wise by grade_a/a2_numerical_check.py")
lines.append("(log grade_a/logs/a2_numerical.log); Fpoly order 0=Psi, 1=Phi1, 2=Phi2,")
lines.append("3=Theta1, 4=Theta2, 5=Theta3 (comparator/Challenge.lean Fpoly).")
lines.append("Core-only (no Mathlib import): scale is Nat, cast to ZMod 32003 at use site.")
lines.append("MS is A1Data.colDataNat, not re-emitted here.")
lines.append("-/")
lines.append("")
lines.append("namespace BranchC.A2Data")
lines.append("")
lines.append("/-- M's 3199 row monomials (t s r u q exponents), in row order. -/")
lines.append("def rowsList : List (Nat × Nat × Nat × Nat × Nat) :=")
lines.append("  [" + ", ".join(tup(r) for r in rows) + "]")
lines.append("")
lines.append("/-- The row monomial of row r, as a 5-tuple. -/")
lines.append("def rowTuple (r : Fin 3199) : Nat × Nat × Nat × Nat × Nat :=")
lines.append("  rowsList.getD r.val (0, 0, 0, 0, 0)")
lines.append("")
lines.append("/-- Pivot columns' generators, in pivot-column order. -/")
lines.append("def genList : List (Fin 6) :=")
lines.append("  [" + ", ".join(str(GENIDX[n]) for n, _ in pivcols) + "]")
lines.append("")
lines.append("/-- The generator of pivot column c. -/")
lines.append("def genFun (c : Fin 3199) : Fin 6 := genList.getD c.val 0")
lines.append("")
lines.append("/-- Pivot columns' multiplier monomials, in pivot-column order. -/")
lines.append("def multList : List (Nat × Nat × Nat × Nat × Nat) :=")
lines.append("  [" + ", ".join(tup(m) for _, m in pivcols) + "]")
lines.append("")
lines.append("/-- The multiplier monomial of pivot column c, as a 5-tuple. -/")
lines.append("def multTuple (c : Fin 3199) : Nat × Nat × Nat × Nat × Nat :=")
lines.append("  multList.getD c.val (0, 0, 0, 0, 0)")
lines.append("")
lines.append("/-- Scale factors c_n (Fpoly_n(w0) = c_n * G_n mod p), in Fpoly order. -/")
lines.append("def scaleList : List Nat := [" + ", ".join(map(str, SCALE)) + "]")
lines.append("")
lines.append("/-- The scale factor of generator n, as a Nat. -/")
lines.append("def scaleFun (n : Fin 6) : Nat := scaleList.getD n.val 0")
lines.append("")
lines.append("end BranchC.A2Data")
lines.append("")

out = os.path.join(BC, "grade_a/lean/GradeA/A2Data.lean")
open(out, "w").write("\n".join(lines))
print(f"wrote {out} ({os.path.getsize(out)} bytes)")
print(f"rows: {len(rows)}, pivcols: {len(pivcols)}, scale: {SCALE}")
