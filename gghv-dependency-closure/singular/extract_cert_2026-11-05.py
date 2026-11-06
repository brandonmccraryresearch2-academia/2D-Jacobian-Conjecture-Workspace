"""Extract the D3 certificate identities from Part11/Part12 and emit Singular checks.

The Lean `have hid : dm1 * (target) = <RHS> := by ring` identity is transcribed
verbatim (Lean polynomial syntax * ^ + - ( ) is valid Singular syntax) into a
Singular script that prints LHS - RHS (must be 0).
"""
import re, sys

def extract(lean_path, vars_line, out_path, label):
    txt = open(lean_path).read()
    m = re.search(r"have hid :(.*?):= by", txt, re.S)
    assert m, lean_path
    stmt = m.group(1)
    # split on the top-level '=' separating LHS from RHS
    depth = 0
    split = None
    for i, ch in enumerate(stmt):
        if ch == '(': depth += 1
        elif ch == ')': depth -= 1
        elif ch == '=' and depth == 0:
            split = i; break
    assert split is not None
    lhs = stmt[:split].strip()
    rhs = stmt[split+1:].strip()
    # sanity: lhs must start with dm1 *
    assert lhs.startswith("dm1 *"), lhs[:40]
    with open(out_path, "w") as f:
        f.write(f"// {label}: D3 certificate identity check, extracted verbatim from {lean_path}\n")
        f.write(vars_line + "\n")
        f.write("poly LHS = " + lhs + ";\n")
        f.write("poly RHS = " + rhs + ";\n")
        f.write('print("CERT_DIFF:");\n')
        f.write("print(LHS - RHS);\n")
        f.write('print("CERT_IS_ZERO (1=yes):");\n')
        f.write("print((LHS - RHS) == 0);\n")
        f.write("quit;\n")
    print(f"wrote {out_path}  (LHS chars={len(lhs)}, RHS chars={len(rhs)})")

extract(
    "/home/hatch/workspace/research/jc2-72-108-exact-certificates/Lean4/JC2/GGHV/Part11_D3Certificate.lean",
    "ring R = 0, (d0,d1,dm1,dm2,dm3,dm4,dm5,dm6,dm7,dm8,dm10,y), dp;",
    "/home/hatch/workspace/research/tooling/d1_singular_cert_s6_2026-11-05.sing",
    "Part11 / GGHV section 6",
)
extract(
    "/home/hatch/workspace/research/jc2-72-108-exact-certificates/Lean4/JC2/GGHV/Part12_D3CertificateS5.lean",
    "ring R = 0, (d0,d1,dm1,dm2,dm3,dm4,dm5,dm6,dm7,dm8,dm10,C3,F), dp;",
    "/home/hatch/workspace/research/tooling/d1_singular_cert_s5_2026-11-05.sing",
    "Part12 / GGHV section 5",
)
