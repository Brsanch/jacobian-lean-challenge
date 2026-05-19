/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftSmoothEndpoints

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # `pwLiftGlobal` is `ContMDiffAt` at every `t ∈ Icc 0 1`

Combines the interior (`Ioo 0 1`) and endpoint (`t = 0`, `t = 1`)
smoothness chips into a single statement: `pwLiftGlobal` is
`ContMDiffAt` at every `t ∈ Icc 0 1`.

## What this file ships

* `ComplexTorus.pwLiftGlobal_contMDiffAt_of_Icc01` — `ContMDiffAt`
  at every `t ∈ Icc 0 1`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`pwLiftGlobal` is `ContMDiffAt` at every `t ∈ Icc 0 1`**. -/
theorem pwLiftGlobal_contMDiffAt_of_Icc01
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) t := by
  -- Case-split: t = 0, t = 1, or t ∈ Ioo 0 1.
  rcases eq_or_lt_of_le ht.1 with h_t_zero | h_t_pos
  · -- t = 0 (and ht.1 says 0 ≤ t, equality means t = 0).
    rw [← h_t_zero]
    exact pwLiftGlobal_contMDiffAt_zero L xs γ h_src N hN h_partition
  · -- t > 0.
    rcases eq_or_lt_of_le ht.2 with h_t_one | h_t_lt_one
    · -- t = 1.
      rw [h_t_one]
      exact pwLiftGlobal_contMDiffAt_one L xs γ h_src N hN h_partition
    · -- t ∈ Ioo 0 1.
      have ht_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨h_t_pos, h_t_lt_one⟩
      have h_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
          (Set.Ioo (0 : ℝ) 1) :=
        pwLiftGlobal_contMDiffOn_Ioo01 L xs γ h_src N hN h_partition
      exact h_on.contMDiffAt (isOpen_Ioo.mem_nhds ht_Ioo)

end ComplexTorus

end JacobianChallenge

end
