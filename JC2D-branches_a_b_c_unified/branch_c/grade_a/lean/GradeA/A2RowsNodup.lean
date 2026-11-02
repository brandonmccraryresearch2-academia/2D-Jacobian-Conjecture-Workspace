/- A2 rowsList Nodup: 32 take/drop chunks, pairwise Bool crosses, flatten assembly. -/
import GradeA.A2Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem nodup_flatten {α : Type} {chunks : List (List α)}
    (h1 : ∀ c ∈ chunks, c.Nodup)
    (h2 : List.Pairwise (fun c₁ c₂ => ∀ a ∈ c₁, ∀ b ∈ c₂, a ≠ b) chunks) :
    (chunks.flatten).Nodup := by
  induction chunks with
  | nil => simp
  | cons c cs ih =>
    have hflat : (c :: cs).flatten = c ++ cs.flatten := rfl
    rw [hflat]
    show List.Pairwise (· ≠ ·) (c ++ cs.flatten)
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact h1 c List.mem_cons_self
    · apply ih
      · intro c' hc'; exact h1 c' (List.mem_cons_of_mem c hc')
      · exact (List.pairwise_cons.mp h2).2
    · intro a ha b hb
      rw [List.mem_flatten] at hb
      obtain ⟨c₂, hc₂, hb⟩ := hb
      exact (List.pairwise_cons.mp h2).1 c₂ hc₂ a ha b hb

theorem chunkNodup00 : (BranchC.A2Data.rowsList.take 100).Nodup := by decide

theorem chunkNodup01 : ((BranchC.A2Data.rowsList.drop 100).take 100).Nodup := by decide

theorem chunkNodup02 : ((BranchC.A2Data.rowsList.drop 200).take 100).Nodup := by decide

theorem chunkNodup03 : ((BranchC.A2Data.rowsList.drop 300).take 100).Nodup := by decide

theorem chunkNodup04 : ((BranchC.A2Data.rowsList.drop 400).take 100).Nodup := by decide

theorem chunkNodup05 : ((BranchC.A2Data.rowsList.drop 500).take 100).Nodup := by decide

theorem chunkNodup06 : ((BranchC.A2Data.rowsList.drop 600).take 100).Nodup := by decide

theorem chunkNodup07 : ((BranchC.A2Data.rowsList.drop 700).take 100).Nodup := by decide

theorem chunkNodup08 : ((BranchC.A2Data.rowsList.drop 800).take 100).Nodup := by decide

theorem chunkNodup09 : ((BranchC.A2Data.rowsList.drop 900).take 100).Nodup := by decide

theorem chunkNodup10 : ((BranchC.A2Data.rowsList.drop 1000).take 100).Nodup := by decide

theorem chunkNodup11 : ((BranchC.A2Data.rowsList.drop 1100).take 100).Nodup := by decide

theorem chunkNodup12 : ((BranchC.A2Data.rowsList.drop 1200).take 100).Nodup := by decide

theorem chunkNodup13 : ((BranchC.A2Data.rowsList.drop 1300).take 100).Nodup := by decide

theorem chunkNodup14 : ((BranchC.A2Data.rowsList.drop 1400).take 100).Nodup := by decide

theorem chunkNodup15 : ((BranchC.A2Data.rowsList.drop 1500).take 100).Nodup := by decide

theorem chunkNodup16 : ((BranchC.A2Data.rowsList.drop 1600).take 100).Nodup := by decide

theorem chunkNodup17 : ((BranchC.A2Data.rowsList.drop 1700).take 100).Nodup := by decide

theorem chunkNodup18 : ((BranchC.A2Data.rowsList.drop 1800).take 100).Nodup := by decide

theorem chunkNodup19 : ((BranchC.A2Data.rowsList.drop 1900).take 100).Nodup := by decide

theorem chunkNodup20 : ((BranchC.A2Data.rowsList.drop 2000).take 100).Nodup := by decide

theorem chunkNodup21 : ((BranchC.A2Data.rowsList.drop 2100).take 100).Nodup := by decide

theorem chunkNodup22 : ((BranchC.A2Data.rowsList.drop 2200).take 100).Nodup := by decide

theorem chunkNodup23 : ((BranchC.A2Data.rowsList.drop 2300).take 100).Nodup := by decide

theorem chunkNodup24 : ((BranchC.A2Data.rowsList.drop 2400).take 100).Nodup := by decide

theorem chunkNodup25 : ((BranchC.A2Data.rowsList.drop 2500).take 100).Nodup := by decide

theorem chunkNodup26 : ((BranchC.A2Data.rowsList.drop 2600).take 100).Nodup := by decide

theorem chunkNodup27 : ((BranchC.A2Data.rowsList.drop 2700).take 100).Nodup := by decide

theorem chunkNodup28 : ((BranchC.A2Data.rowsList.drop 2800).take 100).Nodup := by decide

theorem chunkNodup29 : ((BranchC.A2Data.rowsList.drop 2900).take 100).Nodup := by decide

theorem chunkNodup30 : ((BranchC.A2Data.rowsList.drop 3000).take 100).Nodup := by decide

theorem chunkNodup31 : (BranchC.A2Data.rowsList.drop 3100).Nodup := by decide

theorem crossBool00_01 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_02 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_03 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_04 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_05 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_06 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_07 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_08 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_09 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_10 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_11 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_12 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_13 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_14 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_15 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_16 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_17 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_18 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_19 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_20 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_21 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_22 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_23 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_24 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_25 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_26 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_27 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_28 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_29 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_30 : (BranchC.A2Data.rowsList.take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool00_31 : (BranchC.A2Data.rowsList.take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_02 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_03 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_04 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_05 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_06 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_07 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_08 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_09 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_10 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_11 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_12 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_13 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_14 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_15 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_16 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_17 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_18 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_19 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_20 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_21 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_22 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_23 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_24 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_25 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_26 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_27 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_28 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_29 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_30 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool01_31 : ((BranchC.A2Data.rowsList.drop 100).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_03 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_04 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_05 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_06 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_07 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_08 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_09 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_10 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_11 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_12 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_13 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_14 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_15 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_16 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_17 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_18 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_19 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_20 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_21 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_22 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_23 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_24 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_25 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_26 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_27 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_28 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_29 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_30 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool02_31 : ((BranchC.A2Data.rowsList.drop 200).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_04 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_05 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_06 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_07 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_08 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_09 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_10 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_11 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_12 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_13 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_14 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_15 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_16 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_17 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_18 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_19 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_20 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_21 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_22 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_23 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_24 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_25 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_26 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_27 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_28 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_29 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_30 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool03_31 : ((BranchC.A2Data.rowsList.drop 300).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_05 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_06 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_07 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_08 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_09 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_10 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_11 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_12 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_13 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_14 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_15 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_16 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_17 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_18 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_19 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_20 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_21 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_22 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_23 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_24 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_25 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_26 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_27 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_28 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_29 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_30 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool04_31 : ((BranchC.A2Data.rowsList.drop 400).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_06 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_07 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_08 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_09 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_10 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_11 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_12 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_13 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_14 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_15 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_16 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_17 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_18 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_19 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_20 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_21 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_22 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_23 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_24 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_25 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_26 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_27 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_28 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_29 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_30 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool05_31 : ((BranchC.A2Data.rowsList.drop 500).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_07 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_08 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_09 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_10 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_11 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_12 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_13 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_14 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_15 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_16 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_17 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_18 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_19 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_20 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_21 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_22 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_23 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_24 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_25 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_26 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_27 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_28 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_29 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_30 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool06_31 : ((BranchC.A2Data.rowsList.drop 600).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_08 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_09 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_10 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_11 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_12 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_13 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_14 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_15 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_16 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_17 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_18 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_19 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_20 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_21 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_22 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_23 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_24 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_25 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_26 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_27 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_28 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_29 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_30 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool07_31 : ((BranchC.A2Data.rowsList.drop 700).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_09 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_10 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_11 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_12 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_13 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_14 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_15 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_16 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_17 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_18 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_19 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_20 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_21 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_22 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_23 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_24 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_25 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_26 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_27 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_28 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_29 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_30 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool08_31 : ((BranchC.A2Data.rowsList.drop 800).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_10 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_11 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_12 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_13 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_14 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_15 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_16 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_17 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_18 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_19 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_20 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_21 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_22 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_23 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_24 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_25 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_26 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_27 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_28 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_29 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_30 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool09_31 : ((BranchC.A2Data.rowsList.drop 900).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_11 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_12 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_13 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_14 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_15 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_16 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_17 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_18 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_19 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_20 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_21 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_22 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_23 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_24 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_25 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_26 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_27 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_28 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_29 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_30 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool10_31 : ((BranchC.A2Data.rowsList.drop 1000).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_12 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_13 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_14 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_15 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_16 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_17 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_18 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_19 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_20 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_21 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_22 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_23 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_24 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_25 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_26 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_27 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_28 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_29 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_30 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool11_31 : ((BranchC.A2Data.rowsList.drop 1100).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_13 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_14 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_15 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_16 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_17 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_18 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_19 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_20 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_21 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_22 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_23 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_24 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_25 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_26 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_27 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_28 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_29 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_30 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool12_31 : ((BranchC.A2Data.rowsList.drop 1200).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_14 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_15 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_16 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_17 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_18 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_19 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_20 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_21 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_22 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_23 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_24 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_25 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_26 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_27 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_28 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_29 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_30 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool13_31 : ((BranchC.A2Data.rowsList.drop 1300).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_15 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_16 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_17 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_18 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_19 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_20 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_21 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_22 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_23 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_24 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_25 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_26 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_27 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_28 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_29 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_30 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool14_31 : ((BranchC.A2Data.rowsList.drop 1400).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_16 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_17 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_18 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_19 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_20 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_21 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_22 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_23 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_24 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_25 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_26 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_27 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_28 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_29 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_30 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool15_31 : ((BranchC.A2Data.rowsList.drop 1500).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_17 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_18 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_19 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_20 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_21 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_22 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_23 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_24 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_25 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_26 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_27 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_28 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_29 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_30 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool16_31 : ((BranchC.A2Data.rowsList.drop 1600).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_18 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_19 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_20 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_21 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_22 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_23 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_24 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_25 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_26 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_27 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_28 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_29 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_30 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool17_31 : ((BranchC.A2Data.rowsList.drop 1700).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_19 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_20 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_21 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_22 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_23 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_24 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_25 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_26 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_27 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_28 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_29 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_30 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool18_31 : ((BranchC.A2Data.rowsList.drop 1800).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_20 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_21 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_22 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_23 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_24 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_25 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_26 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_27 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_28 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_29 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_30 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool19_31 : ((BranchC.A2Data.rowsList.drop 1900).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_21 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_22 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_23 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_24 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_25 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_26 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_27 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_28 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_29 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_30 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool20_31 : ((BranchC.A2Data.rowsList.drop 2000).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_22 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_23 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_24 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_25 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_26 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_27 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_28 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_29 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_30 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool21_31 : ((BranchC.A2Data.rowsList.drop 2100).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_23 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_24 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_25 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_26 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_27 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_28 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_29 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_30 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool22_31 : ((BranchC.A2Data.rowsList.drop 2200).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_24 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_25 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_26 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_27 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_28 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_29 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_30 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool23_31 : ((BranchC.A2Data.rowsList.drop 2300).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_25 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_26 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_27 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_28 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_29 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_30 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool24_31 : ((BranchC.A2Data.rowsList.drop 2400).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool25_26 : ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool25_27 : ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool25_28 : ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool25_29 : ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool25_30 : ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool25_31 : ((BranchC.A2Data.rowsList.drop 2500).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool26_27 : ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool26_28 : ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool26_29 : ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool26_30 : ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool26_31 : ((BranchC.A2Data.rowsList.drop 2600).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool27_28 : ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool27_29 : ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool27_30 : ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool27_31 : ((BranchC.A2Data.rowsList.drop 2700).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool28_29 : ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool28_30 : ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool28_31 : ((BranchC.A2Data.rowsList.drop 2800).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool29_30 : ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun a => ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool29_31 : ((BranchC.A2Data.rowsList.drop 2900).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem crossBool30_31 : ((BranchC.A2Data.rowsList.drop 3000).take 100).all (fun a => (BranchC.A2Data.rowsList.drop 3100).all (fun b => decide (a ≠ b))) = true := by decide

theorem cross00_01 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_01 a ha) b hb)

theorem cross00_02 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_02 a ha) b hb)

theorem cross00_03 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_03 a ha) b hb)

theorem cross00_04 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_04 a ha) b hb)

theorem cross00_05 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_05 a ha) b hb)

theorem cross00_06 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_06 a ha) b hb)

theorem cross00_07 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_07 a ha) b hb)

theorem cross00_08 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_08 a ha) b hb)

theorem cross00_09 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_09 a ha) b hb)

theorem cross00_10 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_10 a ha) b hb)

theorem cross00_11 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_11 a ha) b hb)

theorem cross00_12 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_12 a ha) b hb)

theorem cross00_13 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_13 a ha) b hb)

theorem cross00_14 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_14 a ha) b hb)

theorem cross00_15 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_15 a ha) b hb)

theorem cross00_16 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_16 a ha) b hb)

theorem cross00_17 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_17 a ha) b hb)

theorem cross00_18 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_18 a ha) b hb)

theorem cross00_19 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_19 a ha) b hb)

theorem cross00_20 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_20 a ha) b hb)

theorem cross00_21 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_21 a ha) b hb)

theorem cross00_22 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_22 a ha) b hb)

theorem cross00_23 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_23 a ha) b hb)

theorem cross00_24 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_24 a ha) b hb)

theorem cross00_25 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_25 a ha) b hb)

theorem cross00_26 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_26 a ha) b hb)

theorem cross00_27 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_27 a ha) b hb)

theorem cross00_28 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_28 a ha) b hb)

theorem cross00_29 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_29 a ha) b hb)

theorem cross00_30 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_30 a ha) b hb)

theorem cross00_31 : ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool00_31 a ha) b hb)

theorem cross01_02 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_02 a ha) b hb)

theorem cross01_03 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_03 a ha) b hb)

theorem cross01_04 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_04 a ha) b hb)

theorem cross01_05 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_05 a ha) b hb)

theorem cross01_06 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_06 a ha) b hb)

theorem cross01_07 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_07 a ha) b hb)

theorem cross01_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_08 a ha) b hb)

theorem cross01_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_09 a ha) b hb)

theorem cross01_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_10 a ha) b hb)

theorem cross01_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_11 a ha) b hb)

theorem cross01_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_12 a ha) b hb)

theorem cross01_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_13 a ha) b hb)

theorem cross01_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_14 a ha) b hb)

theorem cross01_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_15 a ha) b hb)

theorem cross01_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_16 a ha) b hb)

theorem cross01_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_17 a ha) b hb)

theorem cross01_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_18 a ha) b hb)

theorem cross01_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_19 a ha) b hb)

theorem cross01_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_20 a ha) b hb)

theorem cross01_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_21 a ha) b hb)

theorem cross01_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_22 a ha) b hb)

theorem cross01_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_23 a ha) b hb)

theorem cross01_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_24 a ha) b hb)

theorem cross01_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_25 a ha) b hb)

theorem cross01_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_26 a ha) b hb)

theorem cross01_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_27 a ha) b hb)

theorem cross01_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_28 a ha) b hb)

theorem cross01_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_29 a ha) b hb)

theorem cross01_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_30 a ha) b hb)

theorem cross01_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool01_31 a ha) b hb)

theorem cross02_03 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_03 a ha) b hb)

theorem cross02_04 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_04 a ha) b hb)

theorem cross02_05 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_05 a ha) b hb)

theorem cross02_06 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_06 a ha) b hb)

theorem cross02_07 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_07 a ha) b hb)

theorem cross02_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_08 a ha) b hb)

theorem cross02_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_09 a ha) b hb)

theorem cross02_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_10 a ha) b hb)

theorem cross02_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_11 a ha) b hb)

theorem cross02_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_12 a ha) b hb)

theorem cross02_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_13 a ha) b hb)

theorem cross02_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_14 a ha) b hb)

theorem cross02_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_15 a ha) b hb)

theorem cross02_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_16 a ha) b hb)

theorem cross02_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_17 a ha) b hb)

theorem cross02_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_18 a ha) b hb)

theorem cross02_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_19 a ha) b hb)

theorem cross02_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_20 a ha) b hb)

theorem cross02_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_21 a ha) b hb)

theorem cross02_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_22 a ha) b hb)

theorem cross02_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_23 a ha) b hb)

theorem cross02_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_24 a ha) b hb)

theorem cross02_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_25 a ha) b hb)

theorem cross02_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_26 a ha) b hb)

theorem cross02_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_27 a ha) b hb)

theorem cross02_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_28 a ha) b hb)

theorem cross02_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_29 a ha) b hb)

theorem cross02_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_30 a ha) b hb)

theorem cross02_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool02_31 a ha) b hb)

theorem cross03_04 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_04 a ha) b hb)

theorem cross03_05 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_05 a ha) b hb)

theorem cross03_06 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_06 a ha) b hb)

theorem cross03_07 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_07 a ha) b hb)

theorem cross03_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_08 a ha) b hb)

theorem cross03_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_09 a ha) b hb)

theorem cross03_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_10 a ha) b hb)

theorem cross03_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_11 a ha) b hb)

theorem cross03_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_12 a ha) b hb)

theorem cross03_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_13 a ha) b hb)

theorem cross03_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_14 a ha) b hb)

theorem cross03_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_15 a ha) b hb)

theorem cross03_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_16 a ha) b hb)

theorem cross03_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_17 a ha) b hb)

theorem cross03_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_18 a ha) b hb)

theorem cross03_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_19 a ha) b hb)

theorem cross03_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_20 a ha) b hb)

theorem cross03_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_21 a ha) b hb)

theorem cross03_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_22 a ha) b hb)

theorem cross03_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_23 a ha) b hb)

theorem cross03_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_24 a ha) b hb)

theorem cross03_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_25 a ha) b hb)

theorem cross03_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_26 a ha) b hb)

theorem cross03_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_27 a ha) b hb)

theorem cross03_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_28 a ha) b hb)

theorem cross03_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_29 a ha) b hb)

theorem cross03_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_30 a ha) b hb)

theorem cross03_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool03_31 a ha) b hb)

theorem cross04_05 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_05 a ha) b hb)

theorem cross04_06 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_06 a ha) b hb)

theorem cross04_07 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_07 a ha) b hb)

theorem cross04_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_08 a ha) b hb)

theorem cross04_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_09 a ha) b hb)

theorem cross04_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_10 a ha) b hb)

theorem cross04_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_11 a ha) b hb)

theorem cross04_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_12 a ha) b hb)

theorem cross04_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_13 a ha) b hb)

theorem cross04_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_14 a ha) b hb)

theorem cross04_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_15 a ha) b hb)

theorem cross04_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_16 a ha) b hb)

theorem cross04_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_17 a ha) b hb)

theorem cross04_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_18 a ha) b hb)

theorem cross04_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_19 a ha) b hb)

theorem cross04_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_20 a ha) b hb)

theorem cross04_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_21 a ha) b hb)

theorem cross04_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_22 a ha) b hb)

theorem cross04_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_23 a ha) b hb)

theorem cross04_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_24 a ha) b hb)

theorem cross04_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_25 a ha) b hb)

theorem cross04_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_26 a ha) b hb)

theorem cross04_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_27 a ha) b hb)

theorem cross04_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_28 a ha) b hb)

theorem cross04_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_29 a ha) b hb)

theorem cross04_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_30 a ha) b hb)

theorem cross04_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool04_31 a ha) b hb)

theorem cross05_06 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_06 a ha) b hb)

theorem cross05_07 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_07 a ha) b hb)

theorem cross05_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_08 a ha) b hb)

theorem cross05_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_09 a ha) b hb)

theorem cross05_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_10 a ha) b hb)

theorem cross05_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_11 a ha) b hb)

theorem cross05_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_12 a ha) b hb)

theorem cross05_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_13 a ha) b hb)

theorem cross05_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_14 a ha) b hb)

theorem cross05_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_15 a ha) b hb)

theorem cross05_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_16 a ha) b hb)

theorem cross05_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_17 a ha) b hb)

theorem cross05_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_18 a ha) b hb)

theorem cross05_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_19 a ha) b hb)

theorem cross05_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_20 a ha) b hb)

theorem cross05_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_21 a ha) b hb)

theorem cross05_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_22 a ha) b hb)

theorem cross05_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_23 a ha) b hb)

theorem cross05_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_24 a ha) b hb)

theorem cross05_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_25 a ha) b hb)

theorem cross05_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_26 a ha) b hb)

theorem cross05_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_27 a ha) b hb)

theorem cross05_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_28 a ha) b hb)

theorem cross05_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_29 a ha) b hb)

theorem cross05_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_30 a ha) b hb)

theorem cross05_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool05_31 a ha) b hb)

theorem cross06_07 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_07 a ha) b hb)

theorem cross06_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_08 a ha) b hb)

theorem cross06_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_09 a ha) b hb)

theorem cross06_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_10 a ha) b hb)

theorem cross06_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_11 a ha) b hb)

theorem cross06_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_12 a ha) b hb)

theorem cross06_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_13 a ha) b hb)

theorem cross06_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_14 a ha) b hb)

theorem cross06_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_15 a ha) b hb)

theorem cross06_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_16 a ha) b hb)

theorem cross06_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_17 a ha) b hb)

theorem cross06_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_18 a ha) b hb)

theorem cross06_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_19 a ha) b hb)

theorem cross06_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_20 a ha) b hb)

theorem cross06_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_21 a ha) b hb)

theorem cross06_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_22 a ha) b hb)

theorem cross06_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_23 a ha) b hb)

theorem cross06_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_24 a ha) b hb)

theorem cross06_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_25 a ha) b hb)

theorem cross06_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_26 a ha) b hb)

theorem cross06_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_27 a ha) b hb)

theorem cross06_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_28 a ha) b hb)

theorem cross06_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_29 a ha) b hb)

theorem cross06_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_30 a ha) b hb)

theorem cross06_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool06_31 a ha) b hb)

theorem cross07_08 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_08 a ha) b hb)

theorem cross07_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_09 a ha) b hb)

theorem cross07_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_10 a ha) b hb)

theorem cross07_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_11 a ha) b hb)

theorem cross07_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_12 a ha) b hb)

theorem cross07_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_13 a ha) b hb)

theorem cross07_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_14 a ha) b hb)

theorem cross07_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_15 a ha) b hb)

theorem cross07_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_16 a ha) b hb)

theorem cross07_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_17 a ha) b hb)

theorem cross07_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_18 a ha) b hb)

theorem cross07_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_19 a ha) b hb)

theorem cross07_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_20 a ha) b hb)

theorem cross07_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_21 a ha) b hb)

theorem cross07_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_22 a ha) b hb)

theorem cross07_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_23 a ha) b hb)

theorem cross07_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_24 a ha) b hb)

theorem cross07_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_25 a ha) b hb)

theorem cross07_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_26 a ha) b hb)

theorem cross07_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_27 a ha) b hb)

theorem cross07_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_28 a ha) b hb)

theorem cross07_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_29 a ha) b hb)

theorem cross07_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_30 a ha) b hb)

theorem cross07_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool07_31 a ha) b hb)

theorem cross08_09 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_09 a ha) b hb)

theorem cross08_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_10 a ha) b hb)

theorem cross08_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_11 a ha) b hb)

theorem cross08_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_12 a ha) b hb)

theorem cross08_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_13 a ha) b hb)

theorem cross08_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_14 a ha) b hb)

theorem cross08_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_15 a ha) b hb)

theorem cross08_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_16 a ha) b hb)

theorem cross08_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_17 a ha) b hb)

theorem cross08_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_18 a ha) b hb)

theorem cross08_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_19 a ha) b hb)

theorem cross08_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_20 a ha) b hb)

theorem cross08_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_21 a ha) b hb)

theorem cross08_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_22 a ha) b hb)

theorem cross08_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_23 a ha) b hb)

theorem cross08_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_24 a ha) b hb)

theorem cross08_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_25 a ha) b hb)

theorem cross08_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_26 a ha) b hb)

theorem cross08_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_27 a ha) b hb)

theorem cross08_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_28 a ha) b hb)

theorem cross08_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_29 a ha) b hb)

theorem cross08_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_30 a ha) b hb)

theorem cross08_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool08_31 a ha) b hb)

theorem cross09_10 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_10 a ha) b hb)

theorem cross09_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_11 a ha) b hb)

theorem cross09_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_12 a ha) b hb)

theorem cross09_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_13 a ha) b hb)

theorem cross09_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_14 a ha) b hb)

theorem cross09_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_15 a ha) b hb)

theorem cross09_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_16 a ha) b hb)

theorem cross09_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_17 a ha) b hb)

theorem cross09_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_18 a ha) b hb)

theorem cross09_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_19 a ha) b hb)

theorem cross09_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_20 a ha) b hb)

theorem cross09_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_21 a ha) b hb)

theorem cross09_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_22 a ha) b hb)

theorem cross09_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_23 a ha) b hb)

theorem cross09_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_24 a ha) b hb)

theorem cross09_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_25 a ha) b hb)

theorem cross09_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_26 a ha) b hb)

theorem cross09_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_27 a ha) b hb)

theorem cross09_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_28 a ha) b hb)

theorem cross09_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_29 a ha) b hb)

theorem cross09_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_30 a ha) b hb)

theorem cross09_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool09_31 a ha) b hb)

theorem cross10_11 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_11 a ha) b hb)

theorem cross10_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_12 a ha) b hb)

theorem cross10_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_13 a ha) b hb)

theorem cross10_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_14 a ha) b hb)

theorem cross10_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_15 a ha) b hb)

theorem cross10_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_16 a ha) b hb)

theorem cross10_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_17 a ha) b hb)

theorem cross10_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_18 a ha) b hb)

theorem cross10_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_19 a ha) b hb)

theorem cross10_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_20 a ha) b hb)

theorem cross10_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_21 a ha) b hb)

theorem cross10_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_22 a ha) b hb)

theorem cross10_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_23 a ha) b hb)

theorem cross10_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_24 a ha) b hb)

theorem cross10_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_25 a ha) b hb)

theorem cross10_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_26 a ha) b hb)

theorem cross10_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_27 a ha) b hb)

theorem cross10_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_28 a ha) b hb)

theorem cross10_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_29 a ha) b hb)

theorem cross10_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_30 a ha) b hb)

theorem cross10_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool10_31 a ha) b hb)

theorem cross11_12 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_12 a ha) b hb)

theorem cross11_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_13 a ha) b hb)

theorem cross11_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_14 a ha) b hb)

theorem cross11_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_15 a ha) b hb)

theorem cross11_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_16 a ha) b hb)

theorem cross11_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_17 a ha) b hb)

theorem cross11_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_18 a ha) b hb)

theorem cross11_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_19 a ha) b hb)

theorem cross11_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_20 a ha) b hb)

theorem cross11_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_21 a ha) b hb)

theorem cross11_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_22 a ha) b hb)

theorem cross11_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_23 a ha) b hb)

theorem cross11_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_24 a ha) b hb)

theorem cross11_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_25 a ha) b hb)

theorem cross11_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_26 a ha) b hb)

theorem cross11_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_27 a ha) b hb)

theorem cross11_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_28 a ha) b hb)

theorem cross11_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_29 a ha) b hb)

theorem cross11_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_30 a ha) b hb)

theorem cross11_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool11_31 a ha) b hb)

theorem cross12_13 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_13 a ha) b hb)

theorem cross12_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_14 a ha) b hb)

theorem cross12_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_15 a ha) b hb)

theorem cross12_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_16 a ha) b hb)

theorem cross12_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_17 a ha) b hb)

theorem cross12_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_18 a ha) b hb)

theorem cross12_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_19 a ha) b hb)

theorem cross12_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_20 a ha) b hb)

theorem cross12_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_21 a ha) b hb)

theorem cross12_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_22 a ha) b hb)

theorem cross12_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_23 a ha) b hb)

theorem cross12_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_24 a ha) b hb)

theorem cross12_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_25 a ha) b hb)

theorem cross12_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_26 a ha) b hb)

theorem cross12_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_27 a ha) b hb)

theorem cross12_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_28 a ha) b hb)

theorem cross12_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_29 a ha) b hb)

theorem cross12_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_30 a ha) b hb)

theorem cross12_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool12_31 a ha) b hb)

theorem cross13_14 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_14 a ha) b hb)

theorem cross13_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_15 a ha) b hb)

theorem cross13_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_16 a ha) b hb)

theorem cross13_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_17 a ha) b hb)

theorem cross13_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_18 a ha) b hb)

theorem cross13_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_19 a ha) b hb)

theorem cross13_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_20 a ha) b hb)

theorem cross13_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_21 a ha) b hb)

theorem cross13_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_22 a ha) b hb)

theorem cross13_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_23 a ha) b hb)

theorem cross13_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_24 a ha) b hb)

theorem cross13_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_25 a ha) b hb)

theorem cross13_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_26 a ha) b hb)

theorem cross13_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_27 a ha) b hb)

theorem cross13_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_28 a ha) b hb)

theorem cross13_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_29 a ha) b hb)

theorem cross13_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_30 a ha) b hb)

theorem cross13_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool13_31 a ha) b hb)

theorem cross14_15 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_15 a ha) b hb)

theorem cross14_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_16 a ha) b hb)

theorem cross14_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_17 a ha) b hb)

theorem cross14_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_18 a ha) b hb)

theorem cross14_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_19 a ha) b hb)

theorem cross14_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_20 a ha) b hb)

theorem cross14_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_21 a ha) b hb)

theorem cross14_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_22 a ha) b hb)

theorem cross14_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_23 a ha) b hb)

theorem cross14_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_24 a ha) b hb)

theorem cross14_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_25 a ha) b hb)

theorem cross14_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_26 a ha) b hb)

theorem cross14_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_27 a ha) b hb)

theorem cross14_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_28 a ha) b hb)

theorem cross14_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_29 a ha) b hb)

theorem cross14_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_30 a ha) b hb)

theorem cross14_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool14_31 a ha) b hb)

theorem cross15_16 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_16 a ha) b hb)

theorem cross15_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_17 a ha) b hb)

theorem cross15_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_18 a ha) b hb)

theorem cross15_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_19 a ha) b hb)

theorem cross15_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_20 a ha) b hb)

theorem cross15_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_21 a ha) b hb)

theorem cross15_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_22 a ha) b hb)

theorem cross15_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_23 a ha) b hb)

theorem cross15_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_24 a ha) b hb)

theorem cross15_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_25 a ha) b hb)

theorem cross15_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_26 a ha) b hb)

theorem cross15_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_27 a ha) b hb)

theorem cross15_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_28 a ha) b hb)

theorem cross15_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_29 a ha) b hb)

theorem cross15_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_30 a ha) b hb)

theorem cross15_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool15_31 a ha) b hb)

theorem cross16_17 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_17 a ha) b hb)

theorem cross16_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_18 a ha) b hb)

theorem cross16_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_19 a ha) b hb)

theorem cross16_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_20 a ha) b hb)

theorem cross16_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_21 a ha) b hb)

theorem cross16_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_22 a ha) b hb)

theorem cross16_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_23 a ha) b hb)

theorem cross16_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_24 a ha) b hb)

theorem cross16_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_25 a ha) b hb)

theorem cross16_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_26 a ha) b hb)

theorem cross16_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_27 a ha) b hb)

theorem cross16_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_28 a ha) b hb)

theorem cross16_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_29 a ha) b hb)

theorem cross16_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_30 a ha) b hb)

theorem cross16_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool16_31 a ha) b hb)

theorem cross17_18 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_18 a ha) b hb)

theorem cross17_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_19 a ha) b hb)

theorem cross17_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_20 a ha) b hb)

theorem cross17_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_21 a ha) b hb)

theorem cross17_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_22 a ha) b hb)

theorem cross17_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_23 a ha) b hb)

theorem cross17_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_24 a ha) b hb)

theorem cross17_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_25 a ha) b hb)

theorem cross17_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_26 a ha) b hb)

theorem cross17_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_27 a ha) b hb)

theorem cross17_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_28 a ha) b hb)

theorem cross17_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_29 a ha) b hb)

theorem cross17_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_30 a ha) b hb)

theorem cross17_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool17_31 a ha) b hb)

theorem cross18_19 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_19 a ha) b hb)

theorem cross18_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_20 a ha) b hb)

theorem cross18_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_21 a ha) b hb)

theorem cross18_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_22 a ha) b hb)

theorem cross18_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_23 a ha) b hb)

theorem cross18_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_24 a ha) b hb)

theorem cross18_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_25 a ha) b hb)

theorem cross18_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_26 a ha) b hb)

theorem cross18_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_27 a ha) b hb)

theorem cross18_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_28 a ha) b hb)

theorem cross18_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_29 a ha) b hb)

theorem cross18_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_30 a ha) b hb)

theorem cross18_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool18_31 a ha) b hb)

theorem cross19_20 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_20 a ha) b hb)

theorem cross19_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_21 a ha) b hb)

theorem cross19_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_22 a ha) b hb)

theorem cross19_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_23 a ha) b hb)

theorem cross19_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_24 a ha) b hb)

theorem cross19_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_25 a ha) b hb)

theorem cross19_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_26 a ha) b hb)

theorem cross19_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_27 a ha) b hb)

theorem cross19_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_28 a ha) b hb)

theorem cross19_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_29 a ha) b hb)

theorem cross19_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_30 a ha) b hb)

theorem cross19_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool19_31 a ha) b hb)

theorem cross20_21 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_21 a ha) b hb)

theorem cross20_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_22 a ha) b hb)

theorem cross20_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_23 a ha) b hb)

theorem cross20_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_24 a ha) b hb)

theorem cross20_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_25 a ha) b hb)

theorem cross20_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_26 a ha) b hb)

theorem cross20_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_27 a ha) b hb)

theorem cross20_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_28 a ha) b hb)

theorem cross20_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_29 a ha) b hb)

theorem cross20_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_30 a ha) b hb)

theorem cross20_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool20_31 a ha) b hb)

theorem cross21_22 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_22 a ha) b hb)

theorem cross21_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_23 a ha) b hb)

theorem cross21_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_24 a ha) b hb)

theorem cross21_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_25 a ha) b hb)

theorem cross21_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_26 a ha) b hb)

theorem cross21_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_27 a ha) b hb)

theorem cross21_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_28 a ha) b hb)

theorem cross21_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_29 a ha) b hb)

theorem cross21_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_30 a ha) b hb)

theorem cross21_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool21_31 a ha) b hb)

theorem cross22_23 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_23 a ha) b hb)

theorem cross22_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_24 a ha) b hb)

theorem cross22_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_25 a ha) b hb)

theorem cross22_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_26 a ha) b hb)

theorem cross22_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_27 a ha) b hb)

theorem cross22_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_28 a ha) b hb)

theorem cross22_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_29 a ha) b hb)

theorem cross22_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_30 a ha) b hb)

theorem cross22_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool22_31 a ha) b hb)

theorem cross23_24 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_24 a ha) b hb)

theorem cross23_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_25 a ha) b hb)

theorem cross23_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_26 a ha) b hb)

theorem cross23_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_27 a ha) b hb)

theorem cross23_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_28 a ha) b hb)

theorem cross23_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_29 a ha) b hb)

theorem cross23_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_30 a ha) b hb)

theorem cross23_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool23_31 a ha) b hb)

theorem cross24_25 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_25 a ha) b hb)

theorem cross24_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_26 a ha) b hb)

theorem cross24_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_27 a ha) b hb)

theorem cross24_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_28 a ha) b hb)

theorem cross24_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_29 a ha) b hb)

theorem cross24_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_30 a ha) b hb)

theorem cross24_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool24_31 a ha) b hb)

theorem cross25_26 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool25_26 a ha) b hb)

theorem cross25_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool25_27 a ha) b hb)

theorem cross25_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool25_28 a ha) b hb)

theorem cross25_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool25_29 a ha) b hb)

theorem cross25_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool25_30 a ha) b hb)

theorem cross25_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool25_31 a ha) b hb)

theorem cross26_27 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool26_27 a ha) b hb)

theorem cross26_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool26_28 a ha) b hb)

theorem cross26_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool26_29 a ha) b hb)

theorem cross26_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool26_30 a ha) b hb)

theorem cross26_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool26_31 a ha) b hb)

theorem cross27_28 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool27_28 a ha) b hb)

theorem cross27_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool27_29 a ha) b hb)

theorem cross27_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool27_30 a ha) b hb)

theorem cross27_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool27_31 a ha) b hb)

theorem cross28_29 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool28_29 a ha) b hb)

theorem cross28_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool28_30 a ha) b hb)

theorem cross28_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool28_31 a ha) b hb)

theorem cross29_30 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), ∀ b ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool29_30 a ha) b hb)

theorem cross29_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool29_31 a ha) b hb)

theorem cross30_31 : ∀ a ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), ∀ b ∈ (BranchC.A2Data.rowsList.drop 3100), a ≠ b := by
  intro a ha b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp crossBool30_31 a ha) b hb)

theorem cross_all00 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 100).take 100, (BranchC.A2Data.rowsList.drop 200).take 100, (BranchC.A2Data.rowsList.drop 300).take 100, (BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ (BranchC.A2Data.rowsList.take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross00_01
  · exact cross00_02
  · exact cross00_03
  · exact cross00_04
  · exact cross00_05
  · exact cross00_06
  · exact cross00_07
  · exact cross00_08
  · exact cross00_09
  · exact cross00_10
  · exact cross00_11
  · exact cross00_12
  · exact cross00_13
  · exact cross00_14
  · exact cross00_15
  · exact cross00_16
  · exact cross00_17
  · exact cross00_18
  · exact cross00_19
  · exact cross00_20
  · exact cross00_21
  · exact cross00_22
  · exact cross00_23
  · exact cross00_24
  · exact cross00_25
  · exact cross00_26
  · exact cross00_27
  · exact cross00_28
  · exact cross00_29
  · exact cross00_30
  · exact cross00_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all01 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 200).take 100, (BranchC.A2Data.rowsList.drop 300).take 100, (BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 100).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross01_02
  · exact cross01_03
  · exact cross01_04
  · exact cross01_05
  · exact cross01_06
  · exact cross01_07
  · exact cross01_08
  · exact cross01_09
  · exact cross01_10
  · exact cross01_11
  · exact cross01_12
  · exact cross01_13
  · exact cross01_14
  · exact cross01_15
  · exact cross01_16
  · exact cross01_17
  · exact cross01_18
  · exact cross01_19
  · exact cross01_20
  · exact cross01_21
  · exact cross01_22
  · exact cross01_23
  · exact cross01_24
  · exact cross01_25
  · exact cross01_26
  · exact cross01_27
  · exact cross01_28
  · exact cross01_29
  · exact cross01_30
  · exact cross01_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all02 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 300).take 100, (BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 200).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross02_03
  · exact cross02_04
  · exact cross02_05
  · exact cross02_06
  · exact cross02_07
  · exact cross02_08
  · exact cross02_09
  · exact cross02_10
  · exact cross02_11
  · exact cross02_12
  · exact cross02_13
  · exact cross02_14
  · exact cross02_15
  · exact cross02_16
  · exact cross02_17
  · exact cross02_18
  · exact cross02_19
  · exact cross02_20
  · exact cross02_21
  · exact cross02_22
  · exact cross02_23
  · exact cross02_24
  · exact cross02_25
  · exact cross02_26
  · exact cross02_27
  · exact cross02_28
  · exact cross02_29
  · exact cross02_30
  · exact cross02_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all03 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 300).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross03_04
  · exact cross03_05
  · exact cross03_06
  · exact cross03_07
  · exact cross03_08
  · exact cross03_09
  · exact cross03_10
  · exact cross03_11
  · exact cross03_12
  · exact cross03_13
  · exact cross03_14
  · exact cross03_15
  · exact cross03_16
  · exact cross03_17
  · exact cross03_18
  · exact cross03_19
  · exact cross03_20
  · exact cross03_21
  · exact cross03_22
  · exact cross03_23
  · exact cross03_24
  · exact cross03_25
  · exact cross03_26
  · exact cross03_27
  · exact cross03_28
  · exact cross03_29
  · exact cross03_30
  · exact cross03_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all04 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 400).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross04_05
  · exact cross04_06
  · exact cross04_07
  · exact cross04_08
  · exact cross04_09
  · exact cross04_10
  · exact cross04_11
  · exact cross04_12
  · exact cross04_13
  · exact cross04_14
  · exact cross04_15
  · exact cross04_16
  · exact cross04_17
  · exact cross04_18
  · exact cross04_19
  · exact cross04_20
  · exact cross04_21
  · exact cross04_22
  · exact cross04_23
  · exact cross04_24
  · exact cross04_25
  · exact cross04_26
  · exact cross04_27
  · exact cross04_28
  · exact cross04_29
  · exact cross04_30
  · exact cross04_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all05 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 500).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross05_06
  · exact cross05_07
  · exact cross05_08
  · exact cross05_09
  · exact cross05_10
  · exact cross05_11
  · exact cross05_12
  · exact cross05_13
  · exact cross05_14
  · exact cross05_15
  · exact cross05_16
  · exact cross05_17
  · exact cross05_18
  · exact cross05_19
  · exact cross05_20
  · exact cross05_21
  · exact cross05_22
  · exact cross05_23
  · exact cross05_24
  · exact cross05_25
  · exact cross05_26
  · exact cross05_27
  · exact cross05_28
  · exact cross05_29
  · exact cross05_30
  · exact cross05_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all06 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 600).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross06_07
  · exact cross06_08
  · exact cross06_09
  · exact cross06_10
  · exact cross06_11
  · exact cross06_12
  · exact cross06_13
  · exact cross06_14
  · exact cross06_15
  · exact cross06_16
  · exact cross06_17
  · exact cross06_18
  · exact cross06_19
  · exact cross06_20
  · exact cross06_21
  · exact cross06_22
  · exact cross06_23
  · exact cross06_24
  · exact cross06_25
  · exact cross06_26
  · exact cross06_27
  · exact cross06_28
  · exact cross06_29
  · exact cross06_30
  · exact cross06_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all07 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 700).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross07_08
  · exact cross07_09
  · exact cross07_10
  · exact cross07_11
  · exact cross07_12
  · exact cross07_13
  · exact cross07_14
  · exact cross07_15
  · exact cross07_16
  · exact cross07_17
  · exact cross07_18
  · exact cross07_19
  · exact cross07_20
  · exact cross07_21
  · exact cross07_22
  · exact cross07_23
  · exact cross07_24
  · exact cross07_25
  · exact cross07_26
  · exact cross07_27
  · exact cross07_28
  · exact cross07_29
  · exact cross07_30
  · exact cross07_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all08 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 800).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross08_09
  · exact cross08_10
  · exact cross08_11
  · exact cross08_12
  · exact cross08_13
  · exact cross08_14
  · exact cross08_15
  · exact cross08_16
  · exact cross08_17
  · exact cross08_18
  · exact cross08_19
  · exact cross08_20
  · exact cross08_21
  · exact cross08_22
  · exact cross08_23
  · exact cross08_24
  · exact cross08_25
  · exact cross08_26
  · exact cross08_27
  · exact cross08_28
  · exact cross08_29
  · exact cross08_30
  · exact cross08_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all09 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 900).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross09_10
  · exact cross09_11
  · exact cross09_12
  · exact cross09_13
  · exact cross09_14
  · exact cross09_15
  · exact cross09_16
  · exact cross09_17
  · exact cross09_18
  · exact cross09_19
  · exact cross09_20
  · exact cross09_21
  · exact cross09_22
  · exact cross09_23
  · exact cross09_24
  · exact cross09_25
  · exact cross09_26
  · exact cross09_27
  · exact cross09_28
  · exact cross09_29
  · exact cross09_30
  · exact cross09_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all10 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1000).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross10_11
  · exact cross10_12
  · exact cross10_13
  · exact cross10_14
  · exact cross10_15
  · exact cross10_16
  · exact cross10_17
  · exact cross10_18
  · exact cross10_19
  · exact cross10_20
  · exact cross10_21
  · exact cross10_22
  · exact cross10_23
  · exact cross10_24
  · exact cross10_25
  · exact cross10_26
  · exact cross10_27
  · exact cross10_28
  · exact cross10_29
  · exact cross10_30
  · exact cross10_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all11 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1100).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross11_12
  · exact cross11_13
  · exact cross11_14
  · exact cross11_15
  · exact cross11_16
  · exact cross11_17
  · exact cross11_18
  · exact cross11_19
  · exact cross11_20
  · exact cross11_21
  · exact cross11_22
  · exact cross11_23
  · exact cross11_24
  · exact cross11_25
  · exact cross11_26
  · exact cross11_27
  · exact cross11_28
  · exact cross11_29
  · exact cross11_30
  · exact cross11_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all12 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1200).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross12_13
  · exact cross12_14
  · exact cross12_15
  · exact cross12_16
  · exact cross12_17
  · exact cross12_18
  · exact cross12_19
  · exact cross12_20
  · exact cross12_21
  · exact cross12_22
  · exact cross12_23
  · exact cross12_24
  · exact cross12_25
  · exact cross12_26
  · exact cross12_27
  · exact cross12_28
  · exact cross12_29
  · exact cross12_30
  · exact cross12_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all13 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1300).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross13_14
  · exact cross13_15
  · exact cross13_16
  · exact cross13_17
  · exact cross13_18
  · exact cross13_19
  · exact cross13_20
  · exact cross13_21
  · exact cross13_22
  · exact cross13_23
  · exact cross13_24
  · exact cross13_25
  · exact cross13_26
  · exact cross13_27
  · exact cross13_28
  · exact cross13_29
  · exact cross13_30
  · exact cross13_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all14 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1400).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross14_15
  · exact cross14_16
  · exact cross14_17
  · exact cross14_18
  · exact cross14_19
  · exact cross14_20
  · exact cross14_21
  · exact cross14_22
  · exact cross14_23
  · exact cross14_24
  · exact cross14_25
  · exact cross14_26
  · exact cross14_27
  · exact cross14_28
  · exact cross14_29
  · exact cross14_30
  · exact cross14_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all15 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1500).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross15_16
  · exact cross15_17
  · exact cross15_18
  · exact cross15_19
  · exact cross15_20
  · exact cross15_21
  · exact cross15_22
  · exact cross15_23
  · exact cross15_24
  · exact cross15_25
  · exact cross15_26
  · exact cross15_27
  · exact cross15_28
  · exact cross15_29
  · exact cross15_30
  · exact cross15_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all16 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1600).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross16_17
  · exact cross16_18
  · exact cross16_19
  · exact cross16_20
  · exact cross16_21
  · exact cross16_22
  · exact cross16_23
  · exact cross16_24
  · exact cross16_25
  · exact cross16_26
  · exact cross16_27
  · exact cross16_28
  · exact cross16_29
  · exact cross16_30
  · exact cross16_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all17 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1700).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross17_18
  · exact cross17_19
  · exact cross17_20
  · exact cross17_21
  · exact cross17_22
  · exact cross17_23
  · exact cross17_24
  · exact cross17_25
  · exact cross17_26
  · exact cross17_27
  · exact cross17_28
  · exact cross17_29
  · exact cross17_30
  · exact cross17_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all18 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1800).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross18_19
  · exact cross18_20
  · exact cross18_21
  · exact cross18_22
  · exact cross18_23
  · exact cross18_24
  · exact cross18_25
  · exact cross18_26
  · exact cross18_27
  · exact cross18_28
  · exact cross18_29
  · exact cross18_30
  · exact cross18_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all19 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 1900).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross19_20
  · exact cross19_21
  · exact cross19_22
  · exact cross19_23
  · exact cross19_24
  · exact cross19_25
  · exact cross19_26
  · exact cross19_27
  · exact cross19_28
  · exact cross19_29
  · exact cross19_30
  · exact cross19_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all20 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2000).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross20_21
  · exact cross20_22
  · exact cross20_23
  · exact cross20_24
  · exact cross20_25
  · exact cross20_26
  · exact cross20_27
  · exact cross20_28
  · exact cross20_29
  · exact cross20_30
  · exact cross20_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all21 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2100).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross21_22
  · exact cross21_23
  · exact cross21_24
  · exact cross21_25
  · exact cross21_26
  · exact cross21_27
  · exact cross21_28
  · exact cross21_29
  · exact cross21_30
  · exact cross21_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all22 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2200).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross22_23
  · exact cross22_24
  · exact cross22_25
  · exact cross22_26
  · exact cross22_27
  · exact cross22_28
  · exact cross22_29
  · exact cross22_30
  · exact cross22_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all23 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2300).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross23_24
  · exact cross23_25
  · exact cross23_26
  · exact cross23_27
  · exact cross23_28
  · exact cross23_29
  · exact cross23_30
  · exact cross23_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all24 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2400).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross24_25
  · exact cross24_26
  · exact cross24_27
  · exact cross24_28
  · exact cross24_29
  · exact cross24_30
  · exact cross24_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all25 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2500).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross25_26
  · exact cross25_27
  · exact cross25_28
  · exact cross25_29
  · exact cross25_30
  · exact cross25_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all26 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2600).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact cross26_27
  · exact cross26_28
  · exact cross26_29
  · exact cross26_30
  · exact cross26_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all27 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2700).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | rfl | hc_empty
  · exact cross27_28
  · exact cross27_29
  · exact cross27_30
  · exact cross27_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all28 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2800).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | rfl | hc_empty
  · exact cross28_29
  · exact cross28_30
  · exact cross28_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all29 : ∀ c₂ ∈ [(BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 2900).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | rfl | hc_empty
  · exact cross29_30
  · exact cross29_31
  · exact (List.not_mem_nil hc_empty).elim

theorem cross_all30 : ∀ c₂ ∈ [BranchC.A2Data.rowsList.drop 3100], ∀ a ∈ ((BranchC.A2Data.rowsList.drop 3000).take 100), ∀ b ∈ c₂, a ≠ b := by
  intro c₂ hc₂
  simp only [List.mem_cons] at hc₂
  rcases hc₂ with rfl | hc_empty
  · exact cross30_31
  · exact (List.not_mem_nil hc_empty).elim

theorem h1rows : ∀ c ∈ [BranchC.A2Data.rowsList.take 100, (BranchC.A2Data.rowsList.drop 100).take 100, (BranchC.A2Data.rowsList.drop 200).take 100, (BranchC.A2Data.rowsList.drop 300).take 100, (BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100], c.Nodup := by
  intro c hc
  simp only [List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc_empty
  · exact chunkNodup00
  · exact chunkNodup01
  · exact chunkNodup02
  · exact chunkNodup03
  · exact chunkNodup04
  · exact chunkNodup05
  · exact chunkNodup06
  · exact chunkNodup07
  · exact chunkNodup08
  · exact chunkNodup09
  · exact chunkNodup10
  · exact chunkNodup11
  · exact chunkNodup12
  · exact chunkNodup13
  · exact chunkNodup14
  · exact chunkNodup15
  · exact chunkNodup16
  · exact chunkNodup17
  · exact chunkNodup18
  · exact chunkNodup19
  · exact chunkNodup20
  · exact chunkNodup21
  · exact chunkNodup22
  · exact chunkNodup23
  · exact chunkNodup24
  · exact chunkNodup25
  · exact chunkNodup26
  · exact chunkNodup27
  · exact chunkNodup28
  · exact chunkNodup29
  · exact chunkNodup30
  · exact chunkNodup31
  · exact (List.not_mem_nil hc_empty).elim

theorem h2rows : List.Pairwise
    (fun c₁ c₂ => ∀ a ∈ c₁, ∀ b ∈ c₂, a ≠ b)
    [BranchC.A2Data.rowsList.take 100, (BranchC.A2Data.rowsList.drop 100).take 100, (BranchC.A2Data.rowsList.drop 200).take 100, (BranchC.A2Data.rowsList.drop 300).take 100, (BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100] :=
  (List.pairwise_cons).mpr ⟨cross_all00,
    (List.pairwise_cons).mpr ⟨cross_all01,
      (List.pairwise_cons).mpr ⟨cross_all02,
        (List.pairwise_cons).mpr ⟨cross_all03,
          (List.pairwise_cons).mpr ⟨cross_all04,
            (List.pairwise_cons).mpr ⟨cross_all05,
              (List.pairwise_cons).mpr ⟨cross_all06,
                (List.pairwise_cons).mpr ⟨cross_all07,
                  (List.pairwise_cons).mpr ⟨cross_all08,
                    (List.pairwise_cons).mpr ⟨cross_all09,
                      (List.pairwise_cons).mpr ⟨cross_all10,
                        (List.pairwise_cons).mpr ⟨cross_all11,
                          (List.pairwise_cons).mpr ⟨cross_all12,
                            (List.pairwise_cons).mpr ⟨cross_all13,
                              (List.pairwise_cons).mpr ⟨cross_all14,
                                (List.pairwise_cons).mpr ⟨cross_all15,
                                  (List.pairwise_cons).mpr ⟨cross_all16,
                                    (List.pairwise_cons).mpr ⟨cross_all17,
                                      (List.pairwise_cons).mpr ⟨cross_all18,
                                        (List.pairwise_cons).mpr ⟨cross_all19,
                                          (List.pairwise_cons).mpr ⟨cross_all20,
                                            (List.pairwise_cons).mpr ⟨cross_all21,
                                              (List.pairwise_cons).mpr ⟨cross_all22,
                                                (List.pairwise_cons).mpr ⟨cross_all23,
                                                  (List.pairwise_cons).mpr ⟨cross_all24,
                                                    (List.pairwise_cons).mpr ⟨cross_all25,
                                                      (List.pairwise_cons).mpr ⟨cross_all26,
                                                        (List.pairwise_cons).mpr ⟨cross_all27,
                                                          (List.pairwise_cons).mpr ⟨cross_all28,
                                                            (List.pairwise_cons).mpr ⟨cross_all29,
                                                              (List.pairwise_cons).mpr ⟨cross_all30,
                                                                (List.pairwise_cons).mpr ⟨(fun _c₂ hc₂ => (List.not_mem_nil hc₂).elim), List.Pairwise.nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem rowsNodup : BranchC.A2Data.rowsList.Nodup := by
  have hflat : [BranchC.A2Data.rowsList.take 100, (BranchC.A2Data.rowsList.drop 100).take 100, (BranchC.A2Data.rowsList.drop 200).take 100, (BranchC.A2Data.rowsList.drop 300).take 100, (BranchC.A2Data.rowsList.drop 400).take 100, (BranchC.A2Data.rowsList.drop 500).take 100, (BranchC.A2Data.rowsList.drop 600).take 100, (BranchC.A2Data.rowsList.drop 700).take 100, (BranchC.A2Data.rowsList.drop 800).take 100, (BranchC.A2Data.rowsList.drop 900).take 100, (BranchC.A2Data.rowsList.drop 1000).take 100, (BranchC.A2Data.rowsList.drop 1100).take 100, (BranchC.A2Data.rowsList.drop 1200).take 100, (BranchC.A2Data.rowsList.drop 1300).take 100, (BranchC.A2Data.rowsList.drop 1400).take 100, (BranchC.A2Data.rowsList.drop 1500).take 100, (BranchC.A2Data.rowsList.drop 1600).take 100, (BranchC.A2Data.rowsList.drop 1700).take 100, (BranchC.A2Data.rowsList.drop 1800).take 100, (BranchC.A2Data.rowsList.drop 1900).take 100, (BranchC.A2Data.rowsList.drop 2000).take 100, (BranchC.A2Data.rowsList.drop 2100).take 100, (BranchC.A2Data.rowsList.drop 2200).take 100, (BranchC.A2Data.rowsList.drop 2300).take 100, (BranchC.A2Data.rowsList.drop 2400).take 100, (BranchC.A2Data.rowsList.drop 2500).take 100, (BranchC.A2Data.rowsList.drop 2600).take 100, (BranchC.A2Data.rowsList.drop 2700).take 100, (BranchC.A2Data.rowsList.drop 2800).take 100, (BranchC.A2Data.rowsList.drop 2900).take 100, (BranchC.A2Data.rowsList.drop 3000).take 100, BranchC.A2Data.rowsList.drop 3100].flatten = BranchC.A2Data.rowsList := by decide
  rw [← hflat]
  exact nodup_flatten h1rows h2rows

end BranchC.A2Check
