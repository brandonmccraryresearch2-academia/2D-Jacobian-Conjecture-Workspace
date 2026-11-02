"""emit_a2terms.py -- emit the six chart-generator term lists as core-only Lean data.

Parses grade_a/lean/GradeA/Chart/Gens.lean mechanically (no hand
transcription) and writes grade_a/lean/GradeA/A2Terms.lean:
  structure A2Term (c : Int, i et es er eu eq : Nat)  -- core-only mirror of Chart.Term
  tlPsi, tlPhi1, tlPhi2, tlTheta1, tlTheta2, tlTheta3 : List A2Term
  mono5 : A2Term -> 5-tuple
  termValNat : A2Term -> Nat   -- (c mod 32003) * (11147^i mod 32003) mod 32003
  tlFun : Fin 6 -> List A2Term  -- Fpoly order 0=Psi .. 5=Theta3

Why a mirror instead of importing Chart.Gens: the tuple-level A2 column
checks are core-only (fast kernel decides on Nat tuples), while Gens.lean
imports Chart.Terms, which imports the bundle's ChartProof.Reflect.  The
bridge (List.map toChartTerm A2Terms.tl = Chart.tl, by rfl on literals)
lives in the Mathlib-level A2 file once Chart.Poly is available; this file
is only the data + tuple helpers.  Regenerate if Gens.lean ever changes.
Term counts asserted: Psi 110, Phi1 175, Phi2 175, Theta1/2/3 260 each.
"""
import re, os

BC = os.path.expanduser(
    "~/workspace/research/2D-Jacobian-Conjecture-Workspace/"
    "JC2D-branches_a_b_c_unified/branch_c")
NAMES = [("Psi", "tlPsi", 110), ("Phi1", "tlPhi1", 175), ("Phi2", "tlPhi2", 175),
         ("Theta1", "tlTheta1", 260), ("Theta2", "tlTheta2", 260), ("Theta3", "tlTheta3", 260)]

src = open(os.path.join(BC, "grade_a/lean/GradeA/Chart/Gens.lean")).read()
parsed = {}
for n, _, expect in NAMES:
    start = src.index(f"noncomputable def tl_{n} : List Term :=")
    end = src.index("noncomputable def", start + 10)
    terms = [tuple(map(int, t)) for t in
             re.findall(r"⟨(-?\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+)⟩",
                        src[start:end])]
    assert len(terms) == expect, f"tl_{n}: {len(terms)} != {expect}"
    parsed[n] = terms
    print(f"tl_{n}: {len(terms)} terms OK")

L = []
L.append("/-")
L.append("Chart-generator term lists as core-only data (branch (c)).")
L.append("Emitted by grade_a/emit_a2terms.py by mechanically parsing")
L.append("grade_a/lean/GradeA/Chart/Gens.lean (no hand transcription).")
L.append("A2Term mirrors Chart.Term field for field; the bridge to Chart.tl_*")
L.append("(List.map toChartTerm = tl_*, by rfl on literals) lives in the")
L.append("Mathlib-level A2 file.  Regenerate if Gens.lean ever changes.")
L.append("Core-only: no Mathlib import, no ZMod (values are Nats mod 32003).")
L.append("-/")
L.append("")
L.append("namespace BranchC.A2Terms")
L.append("")
L.append("/-- One term c * w^i * t^et s^es r^er u^eu q^eq, mirroring Chart.Term. -/")
L.append("structure A2Term where")
L.append("  c : Int")
L.append("  i : Nat")
L.append("  et : Nat")
L.append("  es : Nat")
L.append("  er : Nat")
L.append("  eu : Nat")
L.append("  eq : Nat")
L.append("")
for n, lean, _ in NAMES:
    terms = parsed[n]
    body = ", ".join("⟨%d, %d, %d, %d, %d, %d, %d⟩" % t for t in terms)
    L.append(f"/-- Chart generator {n} term list ({len(terms)} terms). -/")
    L.append(f"def {lean} : List A2Term := [{body}]")
    L.append("")
L.append("/-- The term's chart monomial, as a 5-tuple (t s r u q exponents). -/")
L.append("def mono5 (t : A2Term) : Nat × Nat × Nat × Nat × Nat :=")
L.append("  (t.et, t.es, t.er, t.eu, t.eq)")
L.append("")
L.append("/-- The term's value at w0 = 11147 mod 32003, as a Nat. -/")
L.append("def termValNat (t : A2Term) : Nat :=")
L.append("  ((t.c % 32003).toNat * (11147 ^ t.i % 32003)) % 32003")
L.append("")
L.append("/-- Term lists in Fpoly order (0=Psi, 1=Phi1, 2=Phi2, 3=Theta1, 4=Theta2, 5=Theta3). -/")
L.append("def tlFun : Fin 6 → List A2Term")
L.append("  | 0 => tlPsi")
L.append("  | 1 => tlPhi1")
L.append("  | 2 => tlPhi2")
L.append("  | 3 => tlTheta1")
L.append("  | 4 => tlTheta2")
L.append("  | 5 => tlTheta3")
L.append("")
L.append("end BranchC.A2Terms")
L.append("")

out = os.path.join(BC, "grade_a/lean/GradeA/A2Terms.lean")
open(out, "w").write("\n".join(L))
print(f"wrote {out} ({os.path.getsize(out)} bytes)")
