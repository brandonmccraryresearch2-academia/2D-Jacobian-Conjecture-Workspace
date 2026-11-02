/- Probe B: the induction machinery alone (sliceAll as a hypothesis, so
   this file does not need the half files or Mathlib). If this passes,
   the induction is innocent and the killer is elsewhere in the Ind file. -/
import GradeA.HsuppSplitCommon

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

def innerFn (t : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
    (List.range 9).flatMap (fun r =>
      (List.range 9).flatMap (fun u =>
        (List.range 7).map (fun q => (t, s, r, u, q)))))

def countList : List Nat :=
  [491, 427, 373, 323, 277, 237, 203, 169, 143, 119, 97, 79, 65, 50, 40, 31, 23, 17, 13, 8, 6, 4, 2, 1, 1]

def prefixSum : Nat → Nat
  | 0 => 0
  | (n + 1) => prefixSum n + countList.getD n 0

theorem flatMap_append_inner (l₁ l₂ : List Nat) :
    (l₁ ++ l₂).flatMap innerFn = l₁.flatMap innerFn ++ l₂.flatMap innerFn := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.flatMap_cons, ih, List.append_assoc]

theorem filteredPrefixCond
    (hAll : ∀ t : Fin 25,
      ((innerFn t.val).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
        countList.getD t.val 0) :
    ∀ n, n ≤ 25 →
    (((List.range n).flatMap innerFn).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
      prefixSum n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hn' : n ≤ 25 := by omega
    have hstep := ih hn'
    rw [List.range_succ, flatMap_append_inner, List.filter_append, List.length_append, hstep]
    have hsingle : (([n].flatMap innerFn).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
        ((innerFn n).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length := by
      simp [List.flatMap]
    rw [hsingle]
    have hs := hAll ⟨n, by omega⟩
    rw [hs]
    rfl

end BranchC.HsuppSplit
