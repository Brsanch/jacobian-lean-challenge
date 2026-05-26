/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GlobalSolutionCandidate
import JacobianChallenge.Manifold.PartialZBarManifoldFinsetSum

/-! # `partialZBarManifold (globalSolutionCandidate) = Σ_i partialZBarManifold v_i`

Combines:

* Sub-chip 5.4b's `contMDiff_localPompeiuSolutionGlobal` — each
  summand is `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`.
* A chart-pullback differentiability bridge: from manifold
  `ContMDiff` to `DifferentiableAt ℝ (f ∘ extChartAt.symm) (extChartAt x)`
  via `contMDiffOn_extChartAt_symm` + `contMDiffOn_iff_contDiffOn` +
  `ContDiffOn.contDiffAt` + `ContDiffAt.differentiableAt`. Mirrors
  the private lemma `u_chart_x_symm_differentiableAt` in
  `Manifold/ForsterCutoffPoleConstruction.lean`.
* `partialZBarManifold_finset_sum` (just-shipped) — distributivity
  over the finite sum.

Result: for every `y : X`,

```
partialZBarManifold (globalSolutionCandidate P α χs) y
  = ∑ i, partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y.
```

This is the bridge that connects the per-i recovery identities
(Sub-chip 5.4c trilogy + combined per-i identity) to a summed
statement, which Sub-chip 5.6 will combine with the (0,1)-form
transformation rule to derive the final manifold identity.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {cover : FiniteChartCover X}

/-! ## Chart-pullback differentiability bridge -/

/-- For a `ContMDiff` function `u : X → ℂ` and any `x : X`, the chart
pullback `u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm` is `ContDiffOn ℝ ∞` on the
extended-chart target. Mirrors the private
`u_chart_x_symm_contDiffOn` in `ForsterCutoffPoleConstruction.lean`. -/
theorem contDiffOn_extChartAt_pullback_of_contMDiff
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) (x : X) :
    ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
      (extChartAt 𝓘(ℝ, ℂ) x).target := by
  have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (extChartAt 𝓘(ℝ, ℂ) x).symm (extChartAt 𝓘(ℝ, ℂ) x).target :=
    contMDiffOn_extChartAt_symm x
  exact contMDiffOn_iff_contDiffOn.mp (h_u.comp_contMDiffOn h_symm)

/-- For `ContMDiff u` and `y ∈ (chartAt ℂ x).source`,
`u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm` is `DifferentiableAt ℝ` at
`(extChartAt 𝓘(ℂ, ℂ) x) y`. Mirrors the private
`u_chart_x_symm_differentiableAt` pattern in
`Manifold/ForsterCutoffPoleConstruction.lean`. -/
theorem differentiableAt_extChartAt_pullback_of_contMDiff
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) (x y : X)
    (hy : y ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℝ (u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) y) := by
  -- The chart-pullback `u ∘ extChartAt.symm` is the same function for
  -- both models 𝓘(ℝ, ℂ) and 𝓘(ℂ, ℂ) at the type level here, so use
  -- the 𝓘(ℝ, ℂ) `ContDiffOn` and Lean unifies.
  have h_cdo : ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      (extChartAt 𝓘(ℂ, ℂ) x).target :=
    contDiffOn_extChartAt_pullback_of_contMDiff h_u x
  have h_y_tgt : (extChartAt 𝓘(ℂ, ℂ) x) y ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := by
    have hy' : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source := by
      rw [extChartAt_source]; exact hy
    exact (extChartAt 𝓘(ℂ, ℂ) x).map_source hy'
  have h_tgt_open : IsOpen (extChartAt 𝓘(ℂ, ℂ) x).target :=
    isOpen_extChartAt_target x
  have h_at : ContDiffAt ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) y) :=
    (h_cdo _ h_y_tgt).contDiffAt (h_tgt_open.mem_nhds h_y_tgt)
  exact h_at.differentiableAt (by decide)

/-! ## Headline: `partialZBarManifold (Σ v_i) y = Σ partialZBarManifold v_i y` -/

/-- **Manifold-side ∂̄ of the global solution candidate** distributes
over the finite Finset sum: for any `y : X`,

```
partialZBarManifold (globalSolutionCandidate P α χs) y
  = ∑ i, partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y.
```

Each summand's chart-pullback at `y` is `DifferentiableAt ℝ` via
`differentiableAt_extChartAt_pullback_of_contMDiff` + Sub-chip 5.4b's
`contMDiff_localPompeiuSolutionGlobal`; the sum-distributivity is
`partialZBarManifold_finset_sum`. -/
theorem partialZBarManifold_globalSolutionCandidate_eq_finset_sum
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) :
    JacobianChallenge.partialZBarManifold
        (globalSolutionCandidate P α χs) y
      = ∑ i : {x : X // x ∈ cover.basePoints},
          JacobianChallenge.partialZBarManifold
            (localPompeiuSolutionGlobal P i α (χs i)) y := by
  classical
  -- Each summand's chart-pullback at y is DifferentiableAt ℝ.
  have h_diff : ∀ i : {x : X // x ∈ cover.basePoints}, ∀ _ : i ∈ Finset.univ,
      DifferentiableAt ℝ
        (localPompeiuSolutionGlobal P i α (χs i)
            ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
        ((extChartAt 𝓘(ℂ, ℂ) y) y) := by
    intro i _
    have h_v_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (localPompeiuSolutionGlobal P i α (χs i)) :=
      contMDiff_localPompeiuSolutionGlobal P i α h_α (χs i)
    exact differentiableAt_extChartAt_pullback_of_contMDiff h_v_smooth y y
      (mem_chart_source ℂ y)
  -- Apply the Finset-sum distributivity.
  exact partialZBarManifold_finset_sum h_diff

end JacobianChallenge

end
