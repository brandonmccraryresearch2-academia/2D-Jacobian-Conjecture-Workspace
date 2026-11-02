/- Filtered length, v2. Diagnosis of v1 (HsuppSplitFilteredInd):
   ProbeB (induction alone) PASSED, ProbeA (fin_cases + 25-way first-chain)
   DIED rc=137, so the killer is the first-chain dispatch, not the induction.
   This version replaces the chain with a match on the Fin literal: one
   direct exact per arm, zero failed defeq attempts. -/
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

def countList : List Nat :=
  [491, 427, 373, 323, 277, 237, 203, 169, 143, 119, 97, 79, 65, 50, 40, 31, 23, 17, 13, 8, 6, 4, 2, 1, 1]

def prefixSum : Nat → Nat
  | 0 => 0
  | (n + 1) => prefixSum n + countList.getD n 0

theorem sliceAll : ∀ t : Fin 25,
    ((innerFn t.val).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
      countList.getD t.val 0 := by
  intro t
  match t with
  | ⟨0, _⟩ => exact sliceFiltered0
  | ⟨1, _⟩ => exact sliceFiltered1
  | ⟨2, _⟩ => exact sliceFiltered2
  | ⟨3, _⟩ => exact sliceFiltered3
  | ⟨4, _⟩ => exact sliceFiltered4
  | ⟨5, _⟩ => exact sliceFiltered5
  | ⟨6, _⟩ => exact sliceFiltered6
  | ⟨7, _⟩ => exact sliceFiltered7
  | ⟨8, _⟩ => exact sliceFiltered8
  | ⟨9, _⟩ => exact sliceFiltered9
  | ⟨10, _⟩ => exact sliceFiltered10
  | ⟨11, _⟩ => exact sliceFiltered11
  | ⟨12, _⟩ => exact sliceFiltered12
  | ⟨13, _⟩ => exact sliceFiltered13
  | ⟨14, _⟩ => exact sliceFiltered14
  | ⟨15, _⟩ => exact sliceFiltered15
  | ⟨16, _⟩ => exact sliceFiltered16
  | ⟨17, _⟩ => exact sliceFiltered17
  | ⟨18, _⟩ => exact sliceFiltered18
  | ⟨19, _⟩ => exact sliceFiltered19
  | ⟨20, _⟩ => exact sliceFiltered20
  | ⟨21, _⟩ => exact sliceFiltered21
  | ⟨22, _⟩ => exact sliceFiltered22
  | ⟨23, _⟩ => exact sliceFiltered23
  | ⟨24, _⟩ => exact sliceFiltered24
  | ⟨n + 25, h⟩ => exact absurd h (by omega)

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
    (((List.range 25).flatMap innerFn).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 3199 := by
  have h := filteredPrefix 25 (by norm_num)
  rw [h]
  decide

end BranchC.HsuppSplit
