#!/usr/bin/env python3
"""Emit GradeA/A2RowsNodup.lean: Nodup of rowsList via 32 take/drop chunks.

Design (probed v2-v6, all pieces proven before generation):
- 32 chunks of rowsList (100 rows each, last 99) as take/drop expressions;
  no row literals in this file, so no transcription risk.
- Per-chunk Nodup by decide (~10k comparisons each, ~1.4 s).
- All 496 pairwise Bool crosses by decide (~10k each, ~2.3 s), converted
  to forall-form via List.all_eq_true.
- h1 by membership rcases; h2 as a nested pairwise_cons term; generic
  nodup_flatten lemma (induction + pairwise_append + mem_flatten).
- Final theorem via flatten = rowsList by decide (linear).
Single-command ceiling observed: ~250k comparisons survive, ~307k die,
so every decide here is <= ~10k comparisons.
"""
import os

BC = os.path.expanduser(
    "~/workspace/research/2D-Jacobian-Conjecture-Workspace"
    "/JC2D-branches_a_b_c_unified/branch_c")
R = "BranchC.A2Data.rowsList"
NCH = 32


def chunk(i):
    if i == 0:
        return f"{R}.take 100"
    if i < 31:
        return f"({R}.drop {100 * i}).take 100"
    return f"{R}.drop 3100"


CH = [chunk(i) for i in range(NCH)]
CHLIST = "[" + ", ".join(CH) + "]"

out = []
out.append("/- A2 rowsList Nodup: 32 take/drop chunks, pairwise Bool crosses, "
           "flatten assembly. -/")
out.append("import GradeA.A2Data")
out.append("set_option maxRecDepth 1000000")
out.append("set_option maxHeartbeats 4000000")
out.append("")
out.append("namespace BranchC.A2Check")
out.append("")
out.append("theorem nodup_flatten {α : Type} {chunks : List (List α)}")
out.append("    (h1 : ∀ c ∈ chunks, c.Nodup)")
out.append("    (h2 : List.Pairwise (fun c₁ c₂ => ∀ a ∈ c₁, ∀ b ∈ c₂, "
           "a ≠ b) chunks) :")
out.append("    (chunks.flatten).Nodup := by")
out.append("  induction chunks with")
out.append("  | nil => simp")
out.append("  | cons c cs ih =>")
out.append("    have hflat : (c :: cs).flatten = c ++ cs.flatten := rfl")
out.append("    rw [hflat]")
out.append("    show List.Pairwise (· ≠ ·) (c ++ cs.flatten)")
out.append("    rw [List.pairwise_append]")
out.append("    refine ⟨?_, ?_, ?_⟩")
out.append("    · exact h1 c List.mem_cons_self")
out.append("    · apply ih")
out.append("      · intro c' hc'; exact h1 c' (List.mem_cons_of_mem c hc')")
out.append("      · exact (List.pairwise_cons.mp h2).2")
out.append("    · intro a ha b hb")
out.append("      rw [List.mem_flatten] at hb")
out.append("      obtain ⟨c₂, hc₂, hb⟩ := hb")
out.append("      exact (List.pairwise_cons.mp h2).1 c₂ hc₂ a ha b hb")
out.append("")

for i in range(NCH):
    out.append(f"theorem chunkNodup{i:02d} : ({CH[i]}).Nodup := by decide")
    out.append("")

for i in range(NCH):
    for j in range(i + 1, NCH):
        out.append(f"theorem crossBool{i:02d}_{j:02d} : "
                   f"({CH[i]}).all (fun a => ({CH[j]}).all "
                   f"(fun b => decide (a ≠ b))) = true := by decide")
        out.append("")

for i in range(NCH):
    for j in range(i + 1, NCH):
        out.append(f"theorem cross{i:02d}_{j:02d} : "
                   f"∀ a ∈ ({CH[i]}), ∀ b ∈ ({CH[j]}), a ≠ b := by")
        out.append("  intro a ha b hb")
        out.append("  exact of_decide_eq_true (List.all_eq_true.mp "
                   f"(List.all_eq_true.mp crossBool{i:02d}_{j:02d} a ha) b hb)")
        out.append("")

for i in range(NCH - 1):
    tail = "[" + ", ".join(CH[i + 1:]) + "]"
    out.append(f"theorem cross_all{i:02d} : ∀ c₂ ∈ {tail}, "
               f"∀ a ∈ ({CH[i]}), ∀ b ∈ c₂, a ≠ b := by")
    out.append("  intro c₂ hc₂")
    out.append("  simp only [List.mem_cons] at hc₂")
    pats = " | ".join(["rfl"] * (NCH - 1 - i) + ["hc_empty"])
    out.append(f"  rcases hc₂ with {pats}")
    for j in range(i + 1, NCH):
        out.append(f"  · exact cross{i:02d}_{j:02d}")
    out.append("  · exact (List.not_mem_nil hc_empty).elim")
    out.append("")

out.append(f"theorem h1rows : ∀ c ∈ {CHLIST}, c.Nodup := by")
out.append("  intro c hc")
out.append("  simp only [List.mem_cons] at hc")
pats = " | ".join(["rfl"] * NCH + ["hc_empty"])
out.append(f"  rcases hc with {pats}")
for i in range(NCH):
    out.append(f"  · exact chunkNodup{i:02d}")
out.append("  · exact (List.not_mem_nil hc_empty).elim")
out.append("")

out.append("theorem h2rows : List.Pairwise")
out.append("    (fun c₁ c₂ => ∀ a ∈ c₁, ∀ b ∈ c₂, a ≠ b)")
out.append(f"    {CHLIST} :=")
indent = 2
for i in range(NCH - 1):
    out.append(" " * indent +
               f"(List.pairwise_cons).mpr ⟨cross_all{i:02d},")
    indent += 2
out.append(" " * indent +
           "(List.pairwise_cons).mpr ⟨(fun _c₂ hc₂ => "
           "(List.not_mem_nil hc₂).elim), List.Pairwise.nil⟩" +
           "⟩" * (NCH - 1))
out.append("")

out.append("theorem rowsNodup : BranchC.A2Data.rowsList.Nodup := by")
out.append(f"  have hflat : {CHLIST}.flatten = "
           "BranchC.A2Data.rowsList := by decide")
out.append("  rw [← hflat]")
out.append("  exact nodup_flatten h1rows h2rows")
out.append("")
out.append("end BranchC.A2Check")
out.append("")

path = os.path.join(BC, "grade_a/lean/GradeA/A2RowsNodup.lean")
with open(path, "w", encoding="utf-8") as f:
    f.write("\n".join(out))
print(f"wrote {path} ({os.path.getsize(path)} bytes)")
