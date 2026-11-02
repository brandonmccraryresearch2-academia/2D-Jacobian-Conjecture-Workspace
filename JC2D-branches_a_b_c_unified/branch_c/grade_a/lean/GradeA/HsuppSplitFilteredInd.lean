/- Filtered length by induction on the t-prefix.
   The append-chain rfl died rc=137: List defeq is element-wise and
   materializes all 184,275 tuples. Induction keeps everything symbolic:
   no list rfl, no big decides. Slice theorems are reused from the half
   files (defeq: innerFn t unfolds to the same chain as boxSlice t). -/
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

def innerFn (t : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
    (List.range 9).flatMap (fun r =>
      (List.range 9).flatMap (fun u =>
        (List.range 7).map (fun q => (t, s, r, u, q)))))

def boxAll : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 25).flatMap innerFn

def countList : List Nat :=
  [491, 427, 373, 323, 277, 237, 203, 169, 143, 119, 97, 79, 65, 50, 40, 31, 23, 17, 13, 8, 6, 4, 2, 1, 1]

def prefixSum : Nat → Nat
  | 0 => 0
  | (n + 1) => prefixSum n + countList.getD n 0

theorem sliceAll : ∀ t : Fin 25,
    ((innerFn t.val).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
      countList.getD t.val 0 := by
  intro t
  fin_cases t <;> first | exact sliceFiltered0 | exact sliceFiltered1 | exact sliceFiltered2 | exact sliceFiltered3 | exact sliceFiltered4 | exact sliceFiltered5 | exact sliceFiltered6 | exact sliceFiltered7 | exact sliceFiltered8 | exact sliceFiltered9 | exact sliceFiltered10 | exact sliceFiltered11 | exact sliceFiltered12 | exact sliceFiltered13 | exact sliceFiltered14 | exact sliceFiltered15 | exact sliceFiltered16 | exact sliceFiltered17 | exact sliceFiltered18 | exact sliceFiltered19 | exact sliceFiltered20 | exact sliceFiltered21 | exact sliceFiltered22 | exact sliceFiltered23 | exact sliceFiltered24

theorem flatMap_append_inner (l₁ l₂ : List Nat) :
    (l₁ ++ l₂).flatMap innerFn = l₁.flatMap innerFn ++ l₂.flatMap innerFn := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.flatMap_cons, ih, List.append_assoc]

theorem filteredPrefix : ∀ n, n ≤ 25 →
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
    have hs := sliceAll ⟨n, by omega⟩
    rw [hs]
    rfl

theorem filteredLength :
    (boxAll.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 3199 := by
  have h := filteredPrefix 25 (by norm_num)
  rw [show prefixSum 25 = 3199 from by decide] at h
  exact h

end BranchC.HsuppSplit
