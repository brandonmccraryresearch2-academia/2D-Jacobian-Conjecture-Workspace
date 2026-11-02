"""a2_numerical_check.py -- numerical verification of A2 before any Lean work.

A2 (comparator's A2_statement) says, at p = 32003, w0 = 11147:
  (evaluated macaulay block Fpoly/mon/gen/mult) = MS * diagonal(scale o gen)

where mon = M's 3199 rows, (gen, mult) = the 3199 pivot columns (n, m),
MS = the pivot block (INVERSE.pkl colv), and scale(n) = c_n with
Fpoly_n(w0) = c_n * G_n (mod p) monomial-wise (gen_chart.py check 3).

This script verifies that identity numerically, from the actual Lean term
lists (Chart/Gens.lean tl_*) and the rank-check pickles, WITHOUT importing
the bundle: c_n is derived from the m = 0 column of M (one nonzero ratio)
and then checked on every monomial of every generator and every pivot
column.  If this fails, the Lean A2 formalization would be built on wrong
data; if it passes, the Lean work is: emit the data, prove the generic
entry lemma, and decide-check the columns.

Inputs (read-only): grade_a/lean/GradeA/Chart/Gens.lean,
rank_lemma_check/inv_work_M.pkl, rank_lemma_check/INVERSE.pkl.
"""
import sys, re, pickle, os

sys.set_int_max_str_digits(0)
BC = os.path.expanduser(
    "~/workspace/research/2D-Jacobian-Conjecture-Workspace/"
    "JC2D-branches_a_b_c_unified/branch_c")
P, W0 = 32003, 11147
NAMES = ["Psi", "Phi1", "Phi2", "Theta1", "Theta2", "Theta3"]

# 1. Parse the Lean term lists tl_<name> : List Term, entries
#    <c, i, et, es, er, eu, eq>  meaning  c * w^i * t^et s^es r^er u^eu q^eq.
src = open(os.path.join(BC, "grade_a/lean/GradeA/Chart/Gens.lean")).read()
tl = {}
for n in NAMES:
    start = src.index(f"noncomputable def tl_{n} : List Term :=")
    end = src.index("noncomputable def", start + 10)
    block = src[start:end]
    terms = [tuple(map(int, t)) for t in
             re.findall(r"⟨(-?\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+)⟩", block)]
    assert terms, f"tl_{n} empty"
    tl[n] = terms
    print(f"tl_{n}: {len(terms)} terms")

# 2. Evaluated generator dicts: mono (5-tuple) -> value mod p.
ev = {}
for n in NAMES:
    d = {}
    for (c, i, et, es, er, eu, eq) in tl[n]:
        mono = (et, es, er, eu, eq)
        d[mono] = (d.get(mono, 0) + c * pow(W0, i, P)) % P
    ev[n] = {k: v for k, v in d.items() if v}
    print(f"eval {n}: {len(ev[n])} nonzero monomials")

# 3. Rank-check matrix and pivot block.
M = pickle.load(open(os.path.join(BC, "rank_lemma_check/inv_work_M.pkl"), "rb"))
I = pickle.load(open(os.path.join(BC, "rank_lemma_check/INVERSE.pkl"), "rb"))
assert (M["p"], M["w0"]) == (P, W0)
rows, cols, mcolv = M["rows"], M["cols"], M["colv"]
ridx = {r: i for i, r in enumerate(rows)}
piv, pivcols, icolv = I["piv"], I["pivcols"], I["colv"]
assert len(rows) == len(pivcols) == len(icolv) == 3199
assert all(cols[j] == pivcols[jj] for jj, j in enumerate(piv)), "pivcols mismatch"
assert all(dict(mcolv[j]) == dict(icolv[jj]) for jj, j in enumerate(piv)), "MS != M pivot cols"
print("sanity: pivcols match M cols; INVERSE colv == M pivot columns")

# 4. Scale factors c_n, derived from the m = 0 column of M, then checked
#    on every monomial of every generator.
scale = {}
for n in NAMES:
    j0 = cols.index((n, (0, 0, 0, 0, 0)))
    g = dict(mcolv[j0])  # row idx -> G_n value
    gmono = {rows[i]: v for i, v in g.items()}
    assert set(gmono) == set(ev[n]) or True  # compared properly below
    # derive c_n from the first monomial present in both with G != 0
    cn = None
    for mono, gv in gmono.items():
        if gv and mono in ev[n]:
            cn = ev[n][mono] * pow(gv, -1, P) % P
            break
    assert cn is not None and cn != 0, f"no ratio for {n}"
    theirs = {k: v * cn % P for k, v in gmono.items() if v * cn % P}
    assert ev[n] == theirs, f"generator {n}: evaluated tl != c_n * G_n"
    scale[n] = cn
    print(f"scale {n} = {cn}  (checked on {len(ev[n])} monomials)")

# 5. Every pivot column: shifted evaluated dict == scale * MS column dict.
bad = 0
for jj, (n, m) in enumerate(pivcols):
    shifted = {}
    for mono, v in ev[n].items():
        sh = tuple(a + b for a, b in zip(m, mono))
        assert sh in ridx, f"pivot col {jj} ({n},{m}): shifted mono {sh} not a row"
        shifted[ridx[sh]] = v
    ms = dict(icolv[jj])
    expect = {r: v * scale[n] % P for r, v in ms.items()}
    expect = {r: v for r, v in expect.items() if v}
    if shifted != expect:
        bad += 1
        if bad <= 3:
            print(f"MISMATCH col {jj} ({n},{m}): shifted {len(shifted)} vs MS {len(ms)}")
print(f"pivot columns checked: 3199, mismatches: {bad}")
print("A2 NUMERICAL CHECK:", "PASS" if bad == 0 else "FAIL")
