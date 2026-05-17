/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityPointwiseBound

set_option linter.unusedSectionVars false

/-! # Uniform bound on the transition factor over compact chart overlaps

For any compact `K ⊆ (chartAt ℂ x).source ∩ (chartAt ℂ y).source`, the
norm `q ↦ ‖transitionFactor x y q‖` is bounded above on `K`. This is
`continuousOn_transitionFactor` + `IsCompact.exists_bound_of_continuousOn`.

This is the **per-pair compact bound** needed for the convergence-transfer
step: combined with the pointwise density inequality
`norm_localCoeff_le`, it gives a uniform multiplicative bound from
inner-`y` to outer-`x` on `K`.

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Uniform bound on the transition factor over a compact overlap subset.** -/
theorem exists_bound_transitionFactor (x y : X) {K : Set X}
    (hK : IsCompact K)
    (hKx : K ⊆ (chartAt ℂ x).source)
    (hKy : K ⊆ (chartAt ℂ y).source) :
    ∃ C : ℝ, ∀ q ∈ K, ‖transitionFactor x y q‖ ≤ C := by
  refine hK.exists_bound_of_continuousOn ?_
  exact (continuousOn_transitionFactor x y).mono (subset_inter hKx hKy)

/-- **Pointwise density bound on a compact overlap.** Combines the
per-point identity with the uniform transition bound. -/
theorem norm_localCoeff_le_compact_bound
    (om : HolomorphicOneForm X) (x y : X) {K : Set X}
    (hK : IsCompact K)
    (hKx : K ⊆ (chartAt ℂ x).source)
    (hKy : K ⊆ (chartAt ℂ y).source) :
    ∃ C : ℝ, ∀ q ∈ K,
      ‖HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)‖
        ≤ C * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖ := by
  obtain ⟨C, hC⟩ := exists_bound_transitionFactor x y hK hKx hKy
  refine ⟨C, fun q hq => ?_⟩
  have h_id := norm_localCoeff_le om (hKx hq) (hKy hq)
  -- h_id : ‖localCoeff om x ((chartAt x) q)‖
  --        ≤ ‖transitionFactor x y q‖ * ‖localCoeff om y ((chartAt y) q)‖
  -- And ‖transitionFactor x y q‖ ≤ C.
  refine h_id.trans ?_
  -- Goal: ‖τ‖ * ‖localCoeff‖ ≤ C * ‖localCoeff‖.
  have h_nonneg : 0 ≤ ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖ :=
    norm_nonneg _
  exact mul_le_mul_of_nonneg_right (hC q hq) h_nonneg

end DiskChartCover

end JacobianChallenge

end
