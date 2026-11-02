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


def boxSlice13 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (13, s, r, u, q)))))

theorem sliceFiltered13 :
    (boxSlice13.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 50 := by decide

def boxSlice14 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (14, s, r, u, q)))))

theorem sliceFiltered14 :
    (boxSlice14.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 40 := by decide

def boxSlice15 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (15, s, r, u, q)))))

theorem sliceFiltered15 :
    (boxSlice15.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 31 := by decide

def boxSlice16 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (16, s, r, u, q)))))

theorem sliceFiltered16 :
    (boxSlice16.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 23 := by decide

def boxSlice17 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (17, s, r, u, q)))))

theorem sliceFiltered17 :
    (boxSlice17.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 17 := by decide

def boxSlice18 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (18, s, r, u, q)))))

theorem sliceFiltered18 :
    (boxSlice18.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 13 := by decide

def boxSlice19 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (19, s, r, u, q)))))

theorem sliceFiltered19 :
    (boxSlice19.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 8 := by decide

def boxSlice20 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (20, s, r, u, q)))))

theorem sliceFiltered20 :
    (boxSlice20.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 6 := by decide

def boxSlice21 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (21, s, r, u, q)))))

theorem sliceFiltered21 :
    (boxSlice21.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 4 := by decide

def boxSlice22 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (22, s, r, u, q)))))

theorem sliceFiltered22 :
    (boxSlice22.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 2 := by decide

def boxSlice23 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (23, s, r, u, q)))))

theorem sliceFiltered23 :
    (boxSlice23.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 1 := by decide

def boxSlice24 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (24, s, r, u, q)))))

theorem sliceFiltered24 :
    (boxSlice24.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 1 := by decide

end BranchC.HsuppSplit
