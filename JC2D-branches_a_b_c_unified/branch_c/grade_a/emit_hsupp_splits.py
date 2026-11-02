#!/usr/bin/env python3
"""Emit the three Hsupp split files (sliced decides + combiners).

MultDeg/MultQ: 32 uniform slices, slice k = range 100 at base 100*k.
  Slice 31's r=99 case (index 3199) is out of range: getD returns the
  default tuple, whose bound holds trivially (0 <= 19 / 0 <= 4), and the
  combiner never applies r=99 at k=31 (c.val < 3199).
Filtered: 25 t-slices with Python-verified counts summing to 3199.
"""
import os

GA = os.path.expanduser(
    "~/workspace/research/2D-Jacobian-Conjecture-Workspace/"
    "JC2D-branches_a_b_c_unified/branch_c/grade_a/lean/GradeA")

# 2026-11-02: wdeg/qexp live ONLY in HsuppSplitCommon (imported below).
# Every split file used to define them locally, which would clash
# (same fully-qualified name) the moment two split files are imported
# together for assembly. Common has no imports, so it compiles in seconds.
COMMON = """\
/- Shared wdeg/qexp for all Hsupp split files. Defined once, here, so
   split files can be imported together without duplicate-name clashes. -/
namespace BranchC.HsuppSplit

def wdeg (t : Nat × Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2 * t.2.1 + 3 * t.2.2.1 + 3 * t.2.2.2.1 + 4 * t.2.2.2.2

def qexp (t : Nat × Nat × Nat × Nat × Nat) : Nat := t.2.2.2.2

end BranchC.HsuppSplit
"""

HEADER = """\
/- Split decides for Hsupp (see Hsupp.lean): the three full-size decides
   each died rc=137 alone, so each is proved here in small slices plus a
   combiner. One small decide per command; working memory is freed
   between commands. wdeg/qexp come from HsuppSplitCommon (single
   definition, shared so files can be imported together). -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data

"""

IFCHAIN = ("(if genList.getD (100 * %d + r) 0 = 0 then 19 "
           "else if genList.getD (100 * %d + r) 0 = 1 then 18 "
           "else if genList.getD (100 * %d + r) 0 = 2 then 18 else 17)")

# ---------------- MultDeg ----------------
lines = [HEADER]
for k in range(32):
    lines.append(
        f"theorem sliceMultDeg{k} : ∀ r ∈ List.range 100,\n"
        f"    wdeg (multList.getD (100 * {k} + r) (0, 0, 0, 0, 0)) ≤ "
        f"{IFCHAIN % (k, k, k)} := by decide\n")
alts = " | ".join(f"exact sliceMultDeg{k}" for k in range(32))
lines.append(
    "theorem multDegRange : ∀ i ∈ List.range 3199,\n"
    "    wdeg (multList.getD i (0, 0, 0, 0, 0)) ≤\n"
    "      (if genList.getD i 0 = 0 then 19 else if genList.getD i 0 = 1 then 18\n"
    "        else if genList.getD i 0 = 2 then 18 else 17) := by\n"
    "  intro i hi\n"
    "  rw [List.mem_range] at hi\n"
    "  have hk : i / 100 < 32 := by omega\n"
    "  have hr : i % 100 < 100 := Nat.mod_lt _ (by norm_num)\n"
    "  have hEq : 100 * (i / 100) + i % 100 = i := Nat.div_add_mod i 100\n"
    "  have hslice : ∀ k : Fin 32, ∀ r ∈ List.range 100,\n"
    "      wdeg (multList.getD (100 * k.val + r) (0, 0, 0, 0, 0)) ≤\n"
    "        (if genList.getD (100 * k.val + r) 0 = 0 then 19\n"
    "          else if genList.getD (100 * k.val + r) 0 = 1 then 18\n"
    "          else if genList.getD (100 * k.val + r) 0 = 2 then 18 else 17) := by\n"
    f"    intro k; fin_cases k <;> first | {alts}\n"
    "  have h := hslice ⟨i / 100, hk⟩ (i % 100) (List.mem_range.mpr hr)\n"
    "  rw [hEq] at h\n"
    "  exact h\n")
lines.append("end BranchC.HsuppSplit\n")
open(os.path.join(GA, "HsuppSplitMultDeg.lean"), "w").write("\n".join(lines))

# ---------------- MultQ ----------------
lines = [HEADER]
for k in range(32):
    lines.append(
        f"theorem sliceMultQ{k} : ∀ r ∈ List.range 100,\n"
        f"    qexp (multList.getD (100 * {k} + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide\n")
alts = " | ".join(f"exact sliceMultQ{k}" for k in range(32))
lines.append(
    "theorem multQRange : ∀ i ∈ List.range 3199,\n"
    "    qexp (multList.getD i (0, 0, 0, 0, 0)) ≤ 4 := by\n"
    "  intro i hi\n"
    "  rw [List.mem_range] at hi\n"
    "  have hk : i / 100 < 32 := by omega\n"
    "  have hr : i % 100 < 100 := Nat.mod_lt _ (by norm_num)\n"
    "  have hEq : 100 * (i / 100) + i % 100 = i := Nat.div_add_mod i 100\n"
    "  have hslice : ∀ k : Fin 32, ∀ r ∈ List.range 100,\n"
    "      qexp (multList.getD (100 * k.val + r) (0, 0, 0, 0, 0)) ≤ 4 := by\n"
    f"    intro k; fin_cases k <;> first | {alts}\n"
    "  have h := hslice ⟨i / 100, hk⟩ (i % 100) (List.mem_range.mpr hr)\n"
    "  rw [hEq] at h\n"
    "  exact h\n")
lines.append("end BranchC.HsuppSplit\n")
open(os.path.join(GA, "HsuppSplitMultQ.lean"), "w").write("\n".join(lines))

# ---------------- Filtered ----------------
counts = []
for t in range(25):
    c = 0
    for s in range(13):
        for r in range(9):
            for u in range(9):
                for q in range(7):
                    if t + 2 * s + 3 * r + 3 * u + 4 * q <= 24 and q != 6:
                        c += 1
    counts.append(c)
assert sum(counts) == 3199, sum(counts)

INNER = ("(List.range 13).flatMap (fun s =>\n"
         "      (List.range 9).flatMap (fun r =>\n"
         "        (List.range 9).flatMap (fun u =>\n"
         "          (List.range 7).map (fun q => ({t}, s, r, u, q)))))")
PRED = "(fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))"

lines = [HEADER]
lines.append(
    "theorem filterFlatMapLength (l : List Nat)\n"
    "    (f : Nat → List (Nat × Nat × Nat × Nat × Nat)) :\n"
    "    ((l.flatMap f).filter " + PRED + ").length =\n"
    "      (l.map (fun t => ((f t).filter " + PRED + ").length)).sum := by\n"
    "  induction l with\n"
    "  | nil => rfl\n"
    "  | cons a l ih =>\n"
    "    simp only [List.flatMap_cons, List.filter_append, List.length_append,\n"
    "      List.map_cons, List.sum_cons, ih]\n")
# FIX (2026-11-02): attaching .filter directly to the parenthesized inline
# flatMap chain misparses (Lean applies .filter to the lambda, erroring
# `Function.filter`). The validation file's def-form passed, so each slice's
# box is a separate def (same form as the probe's boxList) and the slice
# theorem filters the def. The combiner's show target uses the defs too
# (delta-defeq to the inline terms).
for t in range(25):
    inner = INNER.format(t=t)
    lines.append(
        f"def boxSlice{t} : List (Nat × Nat × Nat × Nat × Nat) :=\n"
        f"  {inner}\n")
    lines.append(
        f"theorem sliceFiltered{t} :\n"
        f"    (boxSlice{t}.filter {PRED}).length = {counts[t]} := by decide\n")
# List.sum is RIGHT-nested: a0 + (a1 + ... + (a24 + 0)). A left-nested
# show target would NOT be defeq (Nat.add assoc is a theorem, not defeq).
def nest(ts):
    if not ts:
        return "0"
    return f"({ts[0]} + {nest(ts[1:])})" if len(ts) > 1 else f"({ts[0]} + 0)"
terms = nest([
    f"((boxSlice{t}.filter {PRED}).length)" for t in range(25)])
lines.append(
    "theorem filteredLength :\n"
    "    (((List.range 25).flatMap (fun t =>\n"
    "      (List.range 13).flatMap (fun s =>\n"
    "        (List.range 9).flatMap (fun r =>\n"
    "          (List.range 9).flatMap (fun u =>\n"
    "            (List.range 7).map (fun q => (t, s, r, u, q))))))).filter "
    + PRED + ").length = 3199 := by\n"
    "  rw [filterFlatMapLength]\n"
    f"  show {terms} = 3199\n"
    + "\n".join(f"  rw [sliceFiltered{t}]" for t in range(25)) + "\n"
    "  norm_num\n")
lines.append("end BranchC.HsuppSplit\n")
open(os.path.join(GA, "HsuppSplitFiltered.lean"), "w").write("\n".join(lines))

# ---------------- MultDeg bisection (diagnosis) ----------------
# Full MultDeg split file died rc=137 (03:22→04:05); MultQ's identical
# combiner pattern passed, so bisect the slices: low half vs high half,
# no combiner, to locate the killing slice range.
for name, ks in [("Low", range(0, 16)), ("High", range(16, 32))]:
    blines = [HEADER]
    for k in ks:
        blines.append(
            f"theorem sliceMultDeg{k} : ∀ r ∈ List.range 100,\n"
            f"    wdeg (multList.getD (100 * {k} + r) (0, 0, 0, 0, 0)) ≤ "
            f"{IFCHAIN % (k, k, k)} := by decide\n")
    blines.append("end BranchC.HsuppSplit\n")
    open(os.path.join(GA, f"HsuppSplitMultDeg{name}.lean"), "w").write("\n".join(blines))
# ---------------- MultDeg quarters + Filtered halves (2026-11-02) ----------------
# High half (16-31) died rc=137 while Low (0-15) passed: quarter it.
# Filtered full split died rc=137 twice: halve its t-slices. Slices only,
# no combiners — these files locate the killing range.
for name, ks in [("Q1", range(16, 24)), ("Q2", range(24, 32))]:
    blines = [HEADER]
    for k in ks:
        blines.append(
            f"theorem sliceMultDeg{k} : ∀ r ∈ List.range 100,\n"
            f"    wdeg (multList.getD (100 * {k} + r) (0, 0, 0, 0, 0)) ≤ "
            f"{IFCHAIN % (k, k, k)} := by decide\n")
    blines.append("end BranchC.HsuppSplit\n")
    open(os.path.join(GA, f"HsuppSplitMultDeg{name}.lean"), "w").write("\n".join(blines))
for name, ts in [("Low", range(0, 13)), ("High", range(13, 25))]:
    flines = [HEADER]
    for t in ts:
        inner = INNER.format(t=t)
        flines.append(
            f"def boxSlice{t} : List (Nat × Nat × Nat × Nat × Nat) :=\n"
            f"  {inner}\n")
        flines.append(
            f"theorem sliceFiltered{t} :\n"
            f"    (boxSlice{t}.filter {PRED}).length = {counts[t]} := by decide\n")
    flines.append("end BranchC.HsuppSplit\n")
    open(os.path.join(GA, f"HsuppSplitFiltered{name}.lean"), "w").write("\n".join(flines))
# ---------------- Common + eighths + assemblers (2026-11-02) ----------------
open(os.path.join(GA, "HsuppSplitCommon.lean"), "w").write(COMMON)
for name, ks in [("E1", range(24, 28)), ("E2", range(28, 32))]:
    blines = [HEADER]
    for k in ks:
        blines.append(
            f"theorem sliceMultDeg{k} : ∀ r ∈ List.range 100,\n"
            f"    wdeg (multList.getD (100 * {k} + r) (0, 0, 0, 0, 0)) ≤ "
            f"{IFCHAIN % (k, k, k)} := by decide\n")
    blines.append("end BranchC.HsuppSplit\n")
    open(os.path.join(GA, f"HsuppSplitMultDeg{name}.lean"), "w").write("\n".join(blines))
# MultDeg assembler: combiner only, no decides; imports the four slice files.
alts = " | ".join(f"exact sliceMultDeg{k}" for k in range(32))
alines = ["""\
/- MultDeg assembler: multDegRange from the imported slice files
   (Low 0-15, Q1 16-23, E1 24-27, E2 28-31). No decides here. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon
import GradeA.HsuppSplitMultDegLow
import GradeA.HsuppSplitMultDegQ1
import GradeA.HsuppSplitMultDegE1
import GradeA.HsuppSplitMultDegE2

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data

""",
    "theorem multDegRange : ∀ i ∈ List.range 3199,\n"
    "    wdeg (multList.getD i (0, 0, 0, 0, 0)) ≤\n"
    "      (if genList.getD i 0 = 0 then 19 else if genList.getD i 0 = 1 then 18\n"
    "        else if genList.getD i 0 = 2 then 18 else 17) := by\n"
    "  intro i hi\n"
    "  rw [List.mem_range] at hi\n"
    "  have hk : i / 100 < 32 := by omega\n"
    "  have hr : i % 100 < 100 := Nat.mod_lt _ (by norm_num)\n"
    "  have hEq : 100 * (i / 100) + i % 100 = i := Nat.div_add_mod i 100\n"
    "  have hslice : ∀ k : Fin 32, ∀ r ∈ List.range 100,\n"
    "      wdeg (multList.getD (100 * k.val + r) (0, 0, 0, 0, 0)) ≤\n"
    "        (if genList.getD (100 * k.val + r) 0 = 0 then 19\n"
    "          else if genList.getD (100 * k.val + r) 0 = 1 then 18\n"
    "          else if genList.getD (100 * k.val + r) 0 = 2 then 18 else 17) := by\n"
    f"    intro k; fin_cases k <;> first | {alts}\n"
    "  have h := hslice ⟨i / 100, hk⟩ (i % 100) (List.mem_range.mpr hr)\n"
    "  rw [hEq] at h\n"
    "  exact h\n",
    "end BranchC.HsuppSplit\n"]
open(os.path.join(GA, "HsuppSplitMultDegAsm.lean"), "w").write("\n".join(alines))
# Filtered assembler: append-chain combiner, no decides; imports both halves.
# FIX (2026-11-02): the first Asm version built the box expression inline
# and miscounted parens (rc=1, unexpected ':='). Use a boxAll def instead
# — the same def-body form the passing boxSlice defs use — so no manual
# paren counting in the statement at all.
BOXALL = ("(List.range 25).flatMap (fun t =>\n"
          "      (List.range 13).flatMap (fun s =>\n"
          "        (List.range 9).flatMap (fun r =>\n"
          "          (List.range 9).flatMap (fun u =>\n"
          "            (List.range 7).map (fun q => (t, s, r, u, q))))))")
CONCAT = " ++ ".join(f"boxSlice{t}" for t in range(25))
flines = ["""\
/- Filtered assembler: filteredLength from the imported half files, via
   an append chain (boxAll = concat of the 25 slice boxes, by rfl on the
   spine) instead of the map-sum show, which is suspect in the full
   file's rc=137 death. No decides here. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon
import GradeA.HsuppSplitFilteredLow
import GradeA.HsuppSplitFilteredHigh

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data

""",
    "def boxAll : List (Nat × Nat × Nat × Nat × Nat) :=\n"
    f"  {BOXALL}\n",
    "theorem filteredLength :\n"
    f"    (boxAll.filter {PRED}).length = 3199 := by\n"
    f"  have hbox : boxAll = {CONCAT} := rfl\n"
    "  rw [hbox]\n"
    "  simp only [List.filter_append, List.length_append]\n"
    + "\n".join(f"  rw [sliceFiltered{t}]" for t in range(25)) + "\n"
    "  norm_num\n",
    "end BranchC.HsuppSplit\n"]
open(os.path.join(GA, "HsuppSplitFilteredAsm.lean"), "w").write("\n".join(flines))
# 50-wide slices for the last 400 indices (2026-11-02): both 100-wide
# pairs at base >= 2800 died rc=137, while 100-wide slices at base <= 2700
# passed — per-slice kernel steps (~100 x avg base) cross the ~250-300k
# cliff at base ~2800. 50-wide slices cost ~50 x base <= ~160k steps.
mlines = [HEADER]
for k in range(8):
    base = 2800 + 50 * k
    mlines.append(
        f"theorem sliceMultDeg50_{k} : ∀ r ∈ List.range 50,\n"
        f"    wdeg (multList.getD ({base} + r) (0, 0, 0, 0, 0)) ≤\n"
        f"      (if genList.getD ({base} + r) 0 = 0 then 19 "
        f"else if genList.getD ({base} + r) 0 = 1 then 18\n"
        f"        else if genList.getD ({base} + r) 0 = 2 then 18 else 17) := by decide\n")
mlines.append("end BranchC.HsuppSplit\n")
open(os.path.join(GA, "HsuppSplitMultDeg50.lean"), "w").write("\n".join(mlines))
# Mixed-width MultDeg assembler: 100-wide slices below 2800 (Fin 28),
# 50-wide slices at/above 2800 (Fin 8). Imports Low, Q1, E1, MultDeg50.
alts28 = " | ".join(f"exact sliceMultDeg{k}" for k in range(28))
alts8 = " | ".join(f"exact sliceMultDeg50_{k}" for k in range(8))
alines2 = ["""\
/- MultDeg assembler (mixed widths): multDegRange from Low (0-15),
   Q1 (16-23), E1 (24-27), and the 50-wide file (2800-3199). No decides. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon
import GradeA.HsuppSplitMultDegLow
import GradeA.HsuppSplitMultDegQ1
import GradeA.HsuppSplitMultDegE1
import GradeA.HsuppSplitMultDeg50

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data

""",
    "theorem multDegRange : ∀ i ∈ List.range 3199,\n"
    "    wdeg (multList.getD i (0, 0, 0, 0, 0)) ≤\n"
    "      (if genList.getD i 0 = 0 then 19 else if genList.getD i 0 = 1 then 18\n"
    "        else if genList.getD i 0 = 2 then 18 else 17) := by\n"
    "  intro i hi\n"
    "  rw [List.mem_range] at hi\n"
    "  have hslice28 : ∀ k : Fin 28, ∀ r ∈ List.range 100,\n"
    "      wdeg (multList.getD (100 * k.val + r) (0, 0, 0, 0, 0)) ≤\n"
    "        (if genList.getD (100 * k.val + r) 0 = 0 then 19\n"
    "          else if genList.getD (100 * k.val + r) 0 = 1 then 18\n"
    "          else if genList.getD (100 * k.val + r) 0 = 2 then 18 else 17) := by\n"
    f"    intro k; fin_cases k <;> first | {alts28}\n"
    "  have hslice8 : ∀ j : Fin 8, ∀ r ∈ List.range 50,\n"
    "      wdeg (multList.getD (2800 + 50 * j.val + r) (0, 0, 0, 0, 0)) ≤\n"
    "        (if genList.getD (2800 + 50 * j.val + r) 0 = 0 then 19\n"
    "          else if genList.getD (2800 + 50 * j.val + r) 0 = 1 then 18\n"
    "          else if genList.getD (2800 + 50 * j.val + r) 0 = 2 then 18 else 17) := by\n"
    f"    intro j; fin_cases j <;> first | {alts8}\n"
    "  by_cases hlt : i < 2800\n"
    "  · have hk : i / 100 < 28 := by omega\n"
    "    have hr : i % 100 < 100 := Nat.mod_lt _ (by norm_num)\n"
    "    have hEq : 100 * (i / 100) + i % 100 = i := Nat.div_add_mod i 100\n"
    "    have h := hslice28 ⟨i / 100, hk⟩ (i % 100) (List.mem_range.mpr hr)\n"
    "    rw [hEq] at h\n"
    "    exact h\n"
    "  · have hj : (i - 2800) / 50 < 8 := by omega\n"
    "    have hr : (i - 2800) % 50 < 50 := Nat.mod_lt _ (by norm_num)\n"
    "    have hEq : 2800 + 50 * ((i - 2800) / 50) + (i - 2800) % 50 = i := by omega\n"
    "    have h := hslice8 ⟨(i - 2800) / 50, hj⟩ ((i - 2800) % 50) (List.mem_range.mpr hr)\n"
    "    rw [hEq] at h\n"
    "    exact h\n",
    "end BranchC.HsuppSplit\n"]
open(os.path.join(GA, "HsuppSplitMultDegAsm2.lean"), "w").write("\n".join(alines2))
# E2 (28-31) died: bisect into pairs (2026-11-02).
for name, ks in [("P1", range(28, 30)), ("P2", range(30, 32))]:
    blines = [HEADER]
    for k in ks:
        blines.append(
            f"theorem sliceMultDeg{k} : ∀ r ∈ List.range 100,\n"
            f"    wdeg (multList.getD (100 * {k} + r) (0, 0, 0, 0, 0)) ≤ "
            f"{IFCHAIN % (k, k, k)} := by decide\n")
    blines.append("end BranchC.HsuppSplit\n")
    open(os.path.join(GA, f"HsuppSplitMultDeg{name}.lean"), "w").write("\n".join(blines))
print("emitted 3 files + 2 bisect files + 2 quarters + 2 halves + Common + 2 eighths + 2 assemblers + 2 pairs; per-t counts sum:", sum(counts))
