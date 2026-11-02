/- Probe: trivial decide over Fin 3199, no check data at all. -/
theorem probeFin : ∀ c : Fin 3199, c.val < 3199 := by
  decide +kernel
