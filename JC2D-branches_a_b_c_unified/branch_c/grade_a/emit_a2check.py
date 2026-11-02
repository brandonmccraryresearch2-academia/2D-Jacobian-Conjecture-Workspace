#!/usr/bin/env python3
"""Emit A2 core-only check data + chunk files.

A2MSPairs.lean: msTuplePairs, the pivot-column entries keyed by row
TUPLE, in INVERSE colv (= A1Data.colDataNat) list order, so linkFun's
list equality holds exactly; the hot check path never pays a
rowsList.getD per entry.

A2TupleCheckBase.lean: tuple-level check defs + generic outside lemmas
+ dedup5 (core has no List.eraseDup) + mem_dedup5_of_mem.
A2TupleCheck{000..319}.lean: 320 chunk theorems (Nat-bounded, 1 per file),
each deciding the tuple check over the column's DEDUPED union tuples
AND the msTuplePairs link for its 10 columns (chunk 319: 9 columns).
Nat form (VALIDATED 2026-10-31: chunk090 passes at 5193 MB, where the
Fin-∀ form died twice at ~6.0 GB): the statement is
∀ (j : Nat) (hj : j < bound), P ⟨base + j, proof⟩, so the kernel
enumerates ONLY the chunk's own values via decidableBallLT, not all
3199 Fin values (the Fin-∀ form's fixed ~1.18 GB enumeration overhead
plus per-column variance put bound-10 Fin chunks at the kill line).
Two Lean quirks, both hit in probes: (1) `∀ hj : j < 10 → BODY` parses
the arrow as part of hj's type (theorem left body-less at `:=`) — use
parenthesized binders with a comma separator; (2) tactic blocks nested
in a ∀-type cannot see the hypothesis binder (v1 omega failure) — the
column bound is a pure term proof referencing hj, plus a standalone
bound lemma per chunk (top-level `by decide` is fine). Asm leaves must
replicate each chunk's proof term EXACTLY (same bound lemma, same hj
name), or the rw [hce] pattern will not match the chunk's statement.
A2TupleCheckAsm.lean: assembly over Fin 3199 (320-level by_cases on
c.val, Nat.sub_lt_left_of_lt_add / Nat.add_sub_cancel' / Fin.ext leaves)
+ the per-tuple check corollary (via mem_dedup5_of_mem) + link corollary.

Core-only throughout (no Mathlib import): the chunk decides run on
plain Nat / 5-tuples.
"""
import pickle, os, sys

BC = os.path.expanduser(
    "~/workspace/research/2D-Jacobian-Conjecture-Workspace/"
    "JC2D-branches_a_b_c_unified/branch_c")
GA = os.path.join(BC, "grade_a", "lean", "GradeA")
RC = os.path.join(BC, "rank_lemma_check")

M = pickle.load(open(os.path.join(RC, "inv_work_M.pkl"), "rb"))
INV = pickle.load(open(os.path.join(RC, "INVERSE.pkl"), "rb"))
rows, cols, colv = M["rows"], M["cols"], M["colv"]
piv = INV["piv"]
p, w0 = M["p"], M["w0"]
assert p == 32003 and w0 == 11147
assert INV["p"] == 32003 and len(piv) == 3199
# pivcols == M cols at piv (sanity, as in the numerical check)
assert all(cols[piv[j]] == INV["pivcols"][j] for j in range(3199))
assert all(dict(colv[piv[j]]) == dict(INV["colv"][j]) for j in range(3199))

def tup(t):
    return "(" + ", ".join(str(x) for x in t) + ")"

# ---- A2MSPairs part files (8 x 400 columns, A1Data pattern) + wrapper ----
# A single 3199-list literal was OOM-killed beside the A2Entry Mathlib
# compile, so the data is split like A1Data's parts.
for part in range(8):
    lo, hi = 400 * part, min(400 * (part + 1), 3199)
    lines = []
    lines.append("/-! Pivot-column entries keyed by row tuple, part %d (core-only). -/" % part)
    lines.append("set_option maxHeartbeats 0")
    lines.append("set_option maxRecDepth 100000")
    lines.append("")
    lines.append("namespace BranchC.A2MSPairs")
    lines.append("")
    lines.append("def msTuplePairsPart%d : List (List ((Nat × Nat × Nat × Nat × Nat) × Nat)) :=" % part)
    lines.append("  [")
    for j in range(lo, hi):
        entries = INV["colv"][j]  # colDataNat order, NOT sorted: linkFun is list equality
        s = "[" + ", ".join("(" + tup(rows[ri]) + ", " + str(v) + ")" for ri, v in entries) + "]"
        lines.append("    " + s + ("," if j < hi - 1 else ""))
    lines.append("  ]")
    lines.append("")
    lines.append("end BranchC.A2MSPairs")
    with open(os.path.join(GA, "A2MSPairs%02d.lean" % part), "w") as f:
        f.write("\n".join(lines) + "\n")
print("A2MSPairs parts written")
wrap = []
wrap.append("/- Pivot-column entries keyed by row tuple (core-only data).")
wrap.append("Emitted by grade_a/emit_a2check.py from inv_work_M.pkl.")
wrap.append("msTuplePairs c = [(rowTuple, value)] for pivot column c. -/")
for part in range(8):
    wrap.append("import GradeA.A2MSPairs%02d" % part)
wrap.append("")
wrap.append("namespace BranchC.A2MSPairs")
wrap.append("")
wrap.append("def msTuplePairs (c : Nat) : List ((Nat × Nat × Nat × Nat × Nat) × Nat) :=")
for part in range(8):
    lo = 400 * part
    if part < 7:
        wrap.append("  if c < %d then msTuplePairsPart%d.getD (c - %d) [] else" % (lo + 400, part, lo))
    else:
        wrap.append("  msTuplePairsPart%d.getD (c - %d) []" % (part, lo))
wrap.append("")
wrap.append("end BranchC.A2MSPairs")
with open(os.path.join(GA, "A2MSPairs.lean"), "w") as f:
    f.write("\n".join(wrap) + "\n")
print("A2MSPairs wrapper written")

# ---- A2TupleCheckBase.lean ----
base = r"""/- A2 tuple-level column check, core-only definitions.

The tuple check: for pivot column `c` and row tuple `rt`,
  tupleSumNatT c rt % 32003 = (msValNatT c rt * scaleFun (genFun c)) % 32003.
`tupleSumNatT` sums `termValNat` over the generator's terms shifted by
`multTuple c`; `msValNatT` sums the emitted `msTuplePairs` entries.
The chunk files decide this over each column's deduped union tuples,
plus the `msTuplePairs` link to `colDataNat` (via `rowTupleOfNat`).
-/
import GradeA.A2Data
import GradeA.A2Terms
import GradeA.A1Data
import GradeA.A2MSPairs

namespace BranchC.A2Check

open BranchC.A2Data BranchC.A2Terms BranchC.A1Data BranchC.A2MSPairs

/-- Term list of the generator of pivot column `c` (A2Term mirror). -/
def colTermsNat (c : Fin 3199) : List A2Term := tlFun (genFun c)

/-- Row tuple by index, with a dummy default (indices < 3199 occur). -/
def rowTupleOfNat (n : Nat) : Nat × Nat × Nat × Nat × Nat :=
  rowsList.getD n (0, 0, 0, 0, 0)

/-- Componentwise addition of 5-tuples (core has no HAdd instance for tuples). -/
def add5 (a b : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)

/-- Tuple sum at `(c, rt)`: evaluated-generator side, in Nat. -/
def tupleSumNatT (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat) : Nat :=
  ((colTermsNat c).map (fun t =>
    if add5 (mono5 t) (multTuple c) = rt then termValNat t else 0)).sum

/-- Tuple sum at `(c, rt)`: MS side, from emitted tuple-keyed pairs. -/
def msValNatT (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat) : Nat :=
  ((msTuplePairs c.val).map (fun t =>
    if t.1 = rt then t.2 else 0)).sum

/-- Shifted term tuples of column `c`. -/
def computedTuples (c : Fin 3199) : List (Nat × Nat × Nat × Nat × Nat) :=
  (colTermsNat c).map (fun t => add5 (mono5 t) (multTuple c))

/-- Union of shifted-term tuples and MS tuples of column `c`. -/
def unionTuples (c : Fin 3199) : List (Nat × Nat × Nat × Nat × Nat) :=
  computedTuples c ++ (msTuplePairs c.val).map Prod.fst

/-- Dedup for 5-tuples (core has no List.eraseDup). The chunk checks run
over `dedup5 (unionTuples c)`: the raw union has ~312 entries with
duplicates but only ~52-70 distinct rows, and each duplicate row
re-scans all 110-260 terms, which is what made bound 100 OOM. -/
def dedup5 (l : List (Nat × Nat × Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat) :=
  l.foldr (fun x acc => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []

/-- Membership in a list implies membership in its dedup. -/
theorem mem_dedup5_of_mem : ∀ (x : Nat × Nat × Nat × Nat × Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat)), x ∈ l → x ∈ dedup5 l := by
  intro x l
  induction l with
  | nil => intro h; simp at h
  | cons a as ih =>
      intro h
      have hstep : dedup5 (a :: as) =
          (if (dedup5 as).any (fun y => decide (a = y)) then dedup5 as
           else a :: dedup5 as) := rfl
      rw [hstep]
      by_cases ha : (dedup5 as).any (fun y => decide (a = y)) = true
      · rw [ite_eq_left ha]
        simp only [List.mem_cons] at h
        cases h with
        | inl hx =>
            rw [List.any_eq_true] at ha
            obtain ⟨y, hy, hy2⟩ := ha
            have hay : a = y := of_decide_eq_true hy2
            rw [hx, hay]
            exact hy
        | inr hx => exact ih hx
      · rw [ite_eq_right ha]
        simp only [List.mem_cons] at h ⊢
        cases h with
        | inl hx => exact Or.inl hx
        | inr hx => exact Or.inr (ih hx)

/-- The per-tuple check predicate, as a Bool. -/
def checkFun (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat) : Bool :=
  tupleSumNatT c rt % 32003 ==
    (msValNatT c rt * scaleFun (genFun c)) % 32003

/-- The `msTuplePairs` link predicate, as a Bool. -/
def linkFun (c : Fin 3199) : Bool :=
  msTuplePairs c.val ==
    (colDataNat c.val).map (fun t => (rowTupleOfNat t.1, t.2))

/-- A Nat list sum is zero when every element is zero (core has no List.sum_eq_zero). -/
theorem nat_sum_eq_zero : ∀ (l : List Nat), (∀ x ∈ l, x = 0) → l.sum = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      rw [List.sum_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

/-- Outside the computed tuples, the tuple sum is zero. -/
theorem tupleSumNatT_zero (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat)
    (h : rt ∉ computedTuples c) : tupleSumNatT c rt = 0 := by
  unfold tupleSumNatT computedTuples at *
  apply nat_sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show (if add5 (mono5 t) (multTuple c) = rt then termValNat t else 0) = 0
  by_cases hc : add5 (mono5 t) (multTuple c) = rt
  · exfalso
    apply h
    rw [List.mem_map]
    exact ⟨t, ht, hc⟩
  · rw [if_neg hc]

/-- Outside the MS tuples, the MS tuple sum is zero. -/
theorem msValNatT_zero (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat)
    (h : rt ∉ (msTuplePairs c.val).map Prod.fst) :
    msValNatT c rt = 0 := by
  unfold msValNatT
  apply nat_sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show (if t.1 = rt then t.2 else 0) = 0
  by_cases hc : t.1 = rt
  · exfalso
    apply h
    rw [List.mem_map]
    exact ⟨t, ht, hc⟩
  · rw [if_neg hc]

end BranchC.A2Check
"""
with open(os.path.join(GA, "A2TupleCheckBase.lean"), "w") as f:
    f.write(base)
print("A2TupleCheckBase.lean written")

# ---- Chunk files: 320 Nat-bounded chunks, 1 per file, deduped union ----
def chunk_proof(k, base):
    if k < 319:
        return (f"Nat.lt_trans (Nat.add_lt_add_left hj {base}) boundChunk{k}")
    return f"Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj {base}) boundChunk{k}"

def chunk_thm(k):
    base = 10 * k
    bound = 10 if k < 319 else 9
    pr = chunk_proof(k, base)
    col = f"⟨{base} + j, {pr}⟩"
    if k < 319:
        bound_thm = (f"theorem boundChunk{k} : ({base} + 10 : Nat) < 3199 := by decide\n")
    else:
        bound_thm = (f"theorem boundChunk{k} : ({base} + 9 : Nat) ≤ 3199 := by decide\n")
    return (bound_thm +
            f"theorem colCheckChunk{k} : ∀ (j : Nat) (hj : j < {bound}),\n"
            f"    (dedup5 (unionTuples {col})).all (checkFun {col}) = true ∧ linkFun {col} = true := by\n"
            f"  decide +kernel")

# Split chunks (failed twice at bound 10): chunk 101 is split at 1015
# into 101a (1010-1014) and 101b (1015-1019), bound 5 each. The split
# range's Asm dispatch gets an inner by_cases at the split point.
SPLITS = {101: 1015, 105: 1055, 107: 1075, 111: 1115, 113: 1135, 114: 1145}
# Pre-split (Brandon, 2026-11-01): every remaining chunk 115..318 at its
# midpoint, after the ~6 GB per-process ceiling killed bound-10 chunks
# 111, 113, 114 even with the balloon at zero. Chunk 319 is deliberately
# NOT split: the generator's split path cannot express it (319b's bound
# lemma would be (3195+5)<3199, false, and Asm's final level has no
# split handling), so it stays bound-9 and is handled if it dies.
SPLITS.update({k: 10 * k + 5 for k in range(115, 319)})
# Quarter-splits (bound-5 halves that themselves exceed the ~6 GB cap,
# first seen in Theta1): QUARTERS[k] = q splits k's b-half at q into
# b1 (s..q-1) and b2 (q..10k+9). Requires k in SPLITS.
QUARTERS = {263: 2637, 264: 2647, 265: 2657, 266: 2667, 267: 2677, 268: 2687, 269: 2697, 270: 2707, 271: 2717, 272: 2727, 276: 2767, 277: 2777, 278: 2787, 279: 2797, 280: 2807, 281: 2817, 282: 2827, 283: 2837, 284: 2847, 285: 2857, 286: 2867, 290: 2907}
# Quarter-splits of A-halves (same cap, first seen in Theta1):
# QUARTERS_A[k] = q splits k's a-half at q into a1 (10k..q-1) and
# a2 (q..s-1). Requires k in SPLITS.
QUARTERS_A = {264: 2642, 265: 2652, 266: 2662, 267: 2672, 268: 2682, 269: 2692, 270: 2702, 271: 2712, 272: 2722, 277: 2772, 279: 2792, 280: 2802, 281: 2812, 282: 2822, 283: 2832, 284: 2842, 285: 2852, 286: 2862}
# 2026-11-01 pre-quarter: every remaining Theta half (chunks 294-318, both
# halves) at half-base+2, replacing the reactive quarter cycle. Quarters are
# 80/80 to date; halves pass only ~1/3 of the time in Theta.
QUARTERS_A.update({k: 10*k+2 for k in range(294, 319)})
QUARTERS.update({k: 10*k+7 for k in range(294, 319)})

def split_thm(suffix, base, bound):
    pr = (f"Nat.lt_trans (Nat.add_lt_add_left hj {base}) boundChunk{suffix}")
    col = f"⟨{base} + j, {pr}⟩"
    bound_thm = (f"theorem boundChunk{suffix} : ({base} + {bound} : Nat) < 3199 := by decide\n")
    return (bound_thm +
            f"theorem colCheckChunk{suffix} : ∀ (j : Nat) (hj : j < {bound}),\n"
            f"    (dedup5 (unionTuples {col})).all (checkFun {col}) = true ∧ linkFun {col} = true := by\n"
            f"  decide +kernel")

for k in range(320):
    if k in SPLITS:
        s = SPLITS[k]
        if k in QUARTERS_A:
            qa = QUARTERS_A[k]
            parts = [(f"{k}a1", 10 * k, qa - 10 * k),
                     (f"{k}a2", qa, s - qa)]
        else:
            parts = [(f"{k}a", 10 * k, s - 10 * k)]
        if k in QUARTERS:
            q = QUARTERS[k]
            parts.append((f"{k}b1", s, q - s))
            parts.append((f"{k}b2", q, 10 * k + 10 - q))
        else:
            parts.append((f"{k}b", s, 10 * k + 10 - s))
        for suffix, base, bound in parts:
            content = ("/- A2 tuple-check chunk %s (core-only, Nat-bounded, deduped). -/\n" % suffix)
            content += "import GradeA.A2TupleCheckBase\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 4000000\n\nnamespace BranchC.A2Check\n\n"
            content += split_thm(suffix, base, bound) + "\n\nend BranchC.A2Check\n"
            with open(os.path.join(GA, "A2TupleCheck%s.lean" % suffix), "w") as f:
                f.write(content)
        continue
    content = ("/- A2 tuple-check chunk %d (core-only, Nat-bounded, deduped). -/\n" % k)
    content += "import GradeA.A2TupleCheckBase\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 4000000\n\nnamespace BranchC.A2Check\n\n"
    content += chunk_thm(k) + "\n\nend BranchC.A2Check\n"
    with open(os.path.join(GA, "A2TupleCheck%03d.lean" % k), "w") as f:
        f.write(content)
print("chunk files written")

# ---- Assembly file: nested by_cases on c.val / 10 ----
asm = r"""/- A2 tuple-check assembly over `Fin 3199` (core-only). -/
import GradeA.A2TupleCheckBase
"""
for k in range(320):
    if k in SPLITS:
        if k in QUARTERS_A:
            asm += "import GradeA.A2TupleCheck%da1\n" % k
            asm += "import GradeA.A2TupleCheck%da2\n" % k
        else:
            asm += "import GradeA.A2TupleCheck%da\n" % k
        if k in QUARTERS:
            asm += "import GradeA.A2TupleCheck%db1\n" % k
            asm += "import GradeA.A2TupleCheck%db2\n" % k
        else:
            asm += "import GradeA.A2TupleCheck%db\n" % k
    else:
        asm += "import GradeA.A2TupleCheck%03d\n" % k
asm += r"""
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

open BranchC.A2Data BranchC.A2Terms BranchC.A1Data BranchC.A2MSPairs

/-- Every column passes its deduped union-tuple check and its link. -/
theorem colCheckAll (c : Fin 3199) :
    (dedup5 (unionTuples c)).all (checkFun c) = true ∧ linkFun c = true := by
"""
# nested by_cases: level k tests c.val < 10*(k+1); last level is chunk 319.
# Leaf for chunk k (base = 10k, bound 10, or 9 for k = 319): the hce
# literal's proof term MUST replicate the chunk statement's proof
# exactly (same bound lemma, same hj name), or rw [hce] will not match.
def asm_leaf(k, J, hhi):
    base = 10 * k
    bound = 10 if k < 319 else 9
    if k == 0:
        hlo_line = f"{J}have hlo : 0 ≤ c.val := Nat.zero_le _\n"
    else:
        hlo_line = f"{J}have hlo : {base} ≤ c.val := Nat.not_lt.mp h{k - 1}\n"
    pr = chunk_proof(k, base)
    lit = f"⟨{base} + (c.val - {base}), {pr}⟩"
    return (hlo_line +
            f"{J}have hj : c.val - {base} < {bound} := Nat.sub_lt_left_of_lt_add hlo {hhi}\n" +
            f"{J}have hck := colCheckChunk{k} (c.val - {base}) hj\n" +
            f"{J}have hval : {base} + (c.val - {base}) = c.val := Nat.add_sub_cancel' hlo\n" +
            f"{J}have hce : ({lit} : Fin 3199) = c := Fin.ext hval\n" +
            f"{J}rw [hce] at hck\n" +
            f"{J}exact hck\n")

def asm_leaf_gen(name, boundname, base, bound, J, hlo_line, hhi):
    pr = f"Nat.lt_trans (Nat.add_lt_add_left hj {base}) {boundname}"
    lit = f"⟨{base} + (c.val - {base}), {pr}⟩"
    return (hlo_line +
            f"{J}have hj : c.val - {base} < {bound} := Nat.sub_lt_left_of_lt_add hlo {hhi}\n" +
            f"{J}have hck := {name} (c.val - {base}) hj\n" +
            f"{J}have hval : {base} + (c.val - {base}) = c.val := Nat.add_sub_cancel' hlo\n" +
            f"{J}have hce : ({lit} : Fin 3199) = c := Fin.ext hval\n" +
            f"{J}rw [hce] at hck\n" +
            f"{J}exact hck\n")

for k in range(319):
    indent = "  " * (k + 1)
    asm += f"{indent}by_cases h{k} : c.val < {10 * (k + 1)}\n"
    asm += f"{indent}·\n"
    if k in SPLITS:
        s = SPLITS[k]
        base = 10 * k
        asm += f"{indent}  by_cases hs{k} : c.val < {s}\n"
        asm += f"{indent}  ·\n"
        if k in QUARTERS_A:
            qa = QUARTERS_A[k]
            asm += f"{indent}    by_cases hs{k}a : c.val < {qa}\n"
            asm += f"{indent}    ·\n"
            asm += asm_leaf_gen(f"colCheckChunk{k}a1", f"boundChunk{k}a1", base, qa - base,
                                "  " * (k + 4),
                                f"{'  ' * (k + 4)}have hlo : {base} ≤ c.val := Nat.not_lt.mp h{k - 1}\n" if k > 0 else f"{'  ' * (k + 4)}have hlo : 0 ≤ c.val := Nat.zero_le _\n",
                                f"hs{k}a")
            asm += f"{indent}    ·\n"
            asm += asm_leaf_gen(f"colCheckChunk{k}a2", f"boundChunk{k}a2", qa, s - qa,
                                "  " * (k + 4),
                                f"{'  ' * (k + 4)}have hlo : {qa} ≤ c.val := Nat.not_lt.mp hs{k}a\n",
                                f"hs{k}")
        else:
            asm += asm_leaf_gen(f"colCheckChunk{k}a", f"boundChunk{k}a", base, s - base,
                                "  " * (k + 3),
                                f"{'  ' * (k + 3)}have hlo : {base} ≤ c.val := Nat.not_lt.mp h{k - 1}\n" if k > 0 else f"{'  ' * (k + 3)}have hlo : 0 ≤ c.val := Nat.zero_le _\n",
                                f"hs{k}")
        asm += f"{indent}  ·\n"
        if k in QUARTERS:
            q = QUARTERS[k]
            asm += f"{indent}    by_cases hs{k}b : c.val < {q}\n"
            asm += f"{indent}    ·\n"
            asm += asm_leaf_gen(f"colCheckChunk{k}b1", f"boundChunk{k}b1", s, q - s,
                                "  " * (k + 4),
                                f"{'  ' * (k + 4)}have hlo : {s} ≤ c.val := Nat.not_lt.mp hs{k}\n",
                                f"hs{k}b")
            asm += f"{indent}    ·\n"
            asm += asm_leaf_gen(f"colCheckChunk{k}b2", f"boundChunk{k}b2", q, 10 * k + 10 - q,
                                "  " * (k + 4),
                                f"{'  ' * (k + 4)}have hlo : {q} ≤ c.val := Nat.not_lt.mp hs{k}b\n",
                                f"h{k}")
        else:
            asm += asm_leaf_gen(f"colCheckChunk{k}b", f"boundChunk{k}b", s, 10 * k + 10 - s,
                                "  " * (k + 3),
                                f"{'  ' * (k + 3)}have hlo : {s} ≤ c.val := Nat.not_lt.mp hs{k}\n",
                                f"h{k}")
    else:
        asm += asm_leaf(k, "  " * (k + 2), f"h{k}")
    asm += f"{indent}·\n"
asm += asm_leaf(319, "  " * 320, "c.isLt")
asm += r"""
/-- Per-tuple check corollary. -/
theorem colCheck (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat)
    (h : rt ∈ unionTuples c) :
    tupleSumNatT c rt % 32003 = (msValNatT c rt * scaleFun (genFun c)) % 32003 := by
  have hall := (colCheckAll c).1
  rw [List.all_eq_true] at hall
  have hb := hall rt (mem_dedup5_of_mem rt (unionTuples c) h)
  exact beq_iff_eq.mp hb

/-- Link corollary. -/
theorem linkAll (c : Fin 3199) :
    msTuplePairs c.val =
      (colDataNat c.val).map (fun t => (rowTupleOfNat t.1, t.2)) := by
  exact beq_iff_eq.mp (colCheckAll c).2

end BranchC.A2Check
"""
with open(os.path.join(GA, "A2TupleCheckAsm.lean"), "w") as f:
    f.write(asm)
print("A2TupleCheckAsm.lean written (no sorry)")
