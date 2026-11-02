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


theorem filterFlatMapLength (l : List Nat)
    (f : Nat → List (Nat × Nat × Nat × Nat × Nat)) :
    ((l.flatMap f).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
      (l.map (fun t => ((f t).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append,
      List.map_cons, List.sum_cons, ih]

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

theorem filteredLength :
    (((List.range 25).flatMap (fun t =>
      (List.range 13).flatMap (fun s =>
        (List.range 9).flatMap (fun r =>
          (List.range 9).flatMap (fun u =>
            (List.range 7).map (fun q => (t, s, r, u, q))))))).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 3199 := by
  rw [filterFlatMapLength]
  show (((boxSlice0.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice1.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice2.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice3.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice4.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice5.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice6.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice7.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice8.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice9.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice10.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice11.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice12.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice13.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice14.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice15.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice16.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice17.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice18.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice19.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice20.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice21.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice22.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice23.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + (((boxSlice24.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length) + 0))))))))))))))))))))))))) = 3199
  rw [sliceFiltered0]
  rw [sliceFiltered1]
  rw [sliceFiltered2]
  rw [sliceFiltered3]
  rw [sliceFiltered4]
  rw [sliceFiltered5]
  rw [sliceFiltered6]
  rw [sliceFiltered7]
  rw [sliceFiltered8]
  rw [sliceFiltered9]
  rw [sliceFiltered10]
  rw [sliceFiltered11]
  rw [sliceFiltered12]
  rw [sliceFiltered13]
  rw [sliceFiltered14]
  rw [sliceFiltered15]
  rw [sliceFiltered16]
  rw [sliceFiltered17]
  rw [sliceFiltered18]
  rw [sliceFiltered19]
  rw [sliceFiltered20]
  rw [sliceFiltered21]
  rw [sliceFiltered22]
  rw [sliceFiltered23]
  rw [sliceFiltered24]
  norm_num

end BranchC.HsuppSplit
