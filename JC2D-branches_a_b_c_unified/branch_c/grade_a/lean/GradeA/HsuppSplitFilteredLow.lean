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


def boxSlice0 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (0, s, r, u, q)))))

theorem sliceFiltered0 :
    (boxSlice0.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 491 := by decide

def boxSlice1 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (1, s, r, u, q)))))

theorem sliceFiltered1 :
    (boxSlice1.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 427 := by decide

def boxSlice2 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (2, s, r, u, q)))))

theorem sliceFiltered2 :
    (boxSlice2.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 373 := by decide

def boxSlice3 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (3, s, r, u, q)))))

theorem sliceFiltered3 :
    (boxSlice3.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 323 := by decide

def boxSlice4 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (4, s, r, u, q)))))

theorem sliceFiltered4 :
    (boxSlice4.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 277 := by decide

def boxSlice5 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (5, s, r, u, q)))))

theorem sliceFiltered5 :
    (boxSlice5.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 237 := by decide

def boxSlice6 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (6, s, r, u, q)))))

theorem sliceFiltered6 :
    (boxSlice6.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 203 := by decide

def boxSlice7 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (7, s, r, u, q)))))

theorem sliceFiltered7 :
    (boxSlice7.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 169 := by decide

def boxSlice8 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (8, s, r, u, q)))))

theorem sliceFiltered8 :
    (boxSlice8.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 143 := by decide

def boxSlice9 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (9, s, r, u, q)))))

theorem sliceFiltered9 :
    (boxSlice9.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 119 := by decide

def boxSlice10 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (10, s, r, u, q)))))

theorem sliceFiltered10 :
    (boxSlice10.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 97 := by decide

def boxSlice11 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (11, s, r, u, q)))))

theorem sliceFiltered11 :
    (boxSlice11.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 79 := by decide

def boxSlice12 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (12, s, r, u, q)))))

theorem sliceFiltered12 :
    (boxSlice12.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 65 := by decide

end BranchC.HsuppSplit
