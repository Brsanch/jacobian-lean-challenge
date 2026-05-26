/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionManifoldIdentity
import JacobianChallenge.Manifold.PartialZBarManifoldAtChart

/-! # Sub-chip 5.5b — combined per-i identity in the chart-anchored frame

The combined per-`i` recovery (Sub-chip 5.4 trilogy + assembly layer)
delivers, on `support (P.rhoC i)`,

```
partialZBarManifold v_i y
    · conj(deriv (chartAt ℂ y ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y))
  = (P.rhoC i * α) y
```

— a chart-y-anchored statement whose conj-derivative transition factor
varies with `i` and obstructs the partition-of-unity sum.

Sub-chip 5.5a (Path A) introduced the chart-anchored operator
`partialZBarManifoldAtChart`. **In that frame the recovery identity is
factor-free**: re-evaluated through chart-x_i (the chart used to
construct `v_i`), the chain-rule factor is never produced. This file
ships that statement:

```
partialZBarManifoldAtChart i.val v_i y = (P.rhoC i * α) y
                                                   on `support (P.rhoC i)`.
```

The proof reuses Sub-chip 5.4c-prep's local-coincidence
(`v_i =ᶠ[𝓝 y] chartPompeiuSolution i P α` on `support (P.rhoC i)`)
together with the chart-x_i view evaluation from Sub-chip 5.4c-final
(`partialZBar_chartPompeiuSolution_chart_xi_symm_eq`), bridged by
germ-dependence of `partialZBar` after composition with
`(chartAt ℂ i.val).symm` (continuous at the chart image of `y`).

This is the first per-`i` identity in the chart-anchored frame; the
partition-sum machinery (Sub-chip 5.5c) consumes it directly without
the chart-transition algebra.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function Filter
open JacobianChallenge.PompeiuKernel

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {cover : FiniteChartCover X}

/-! ## Germ-respecting `partialZBarManifoldAtChart`

A short helper: `partialZBarManifoldAtChart x` only depends on the
germ of `f` at `y` (via `chart_x.symm`-continuity at `chart_x y` for
`y ∈ chart_x.source`). This is the chart-anchored analogue of
`partialZBarManifold_eventuallyEq_congr` from
`LocalPompeiuSolutionGlobalPartialZBar.lean`. -/
theorem partialZBarManifoldAtChart_eventuallyEq_congr
    {f g : X → ℂ} {x y : X} (hy : y ∈ (chartAt ℂ x).source)
    (h : f =ᶠ[𝓝 y] g) :
    partialZBarManifoldAtChart x f y = partialZBarManifoldAtChart x g y := by
  unfold partialZBarManifoldAtChart
  -- chart_x.symm is continuous at chart_x y (since chart_x y ∈ chart_x.target).
  have h_target : (chartAt ℂ x) y ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source hy
  have h_cts : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) y) :=
    (chartAt ℂ x).continuousAt_symm h_target
  -- chart_x.symm sends chart_x y back to y by left_inv.
  have h_symm_apply : (chartAt ℂ x).symm ((chartAt ℂ x) y) = y :=
    (chartAt ℂ x).left_inv hy
  -- Lift to Tendsto in nhds y.
  have h_tendsto : Filter.Tendsto (chartAt ℂ x).symm
      (𝓝 ((chartAt ℂ x) y)) (𝓝 y) := by
    have := h_cts
    rwa [ContinuousAt, h_symm_apply] at this
  -- Compose with the original eventual equality.
  have h_comp : (f ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 ((chartAt ℂ x) y)]
      (g ∘ (chartAt ℂ x).symm) :=
    h.comp_tendsto h_tendsto
  -- partialZBar depends only on the germ.
  unfold partialZBar
  rw [Filter.EventuallyEq.fderiv_eq h_comp]

/-! ## Headline — chart-anchored per-i recovery identity (factor-free) -/

/-- **Sub-chip 5.5b.** Chart-anchored per-`i` recovery identity. For
`y ∈ support (P.rhoC i)`,

```
partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
  = (P.rhoC i * α) y
```

— **no chart-transition factor on the RHS**. Anchoring the
manifold-side `∂̄` in the construction chart `(chartAt ℂ i.val)` (the
same chart used to build `v_i` via the Pompeiu kernel) absorbs the
chain-rule artifact that appeared in
`partialZBarManifold_localPompeiuSolutionGlobal_eq_α_mul_transition_on_support_rhoC`.

Proof: combine the existing local-coincidence
(`localPompeiuSolutionGlobal_eventuallyEq_chartPompeiuSolution_on_support_rhoC`,
Sub-chip 5.4c-prep) — saying `v_i =ᶠ[𝓝 y] chartPompeiuSolution i P α`
on the open set `support (P.rhoC i)` — with the chart-x_i view
evaluation
(`partialZBar_chartPompeiuSolution_chart_xi_symm_eq`, Sub-chip 5.4c-final),
bridged by germ-dependence of `partialZBarManifoldAtChart i.val`
(`partialZBarManifoldAtChart_eventuallyEq_congr` above). The
hypothesis `y ∈ (chartAt ℂ i.val).source` needed by the germ-bridge
is supplied by `support_rhoC_subset_chart_source` from the assembly
layer. -/
theorem partialZBarManifoldAtChart_localPompeiuSolutionGlobal_eq_rhoC_mul_alpha_on_support_rhoC
    [CompactSpace X]
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∈ Function.support (P.rhoC i)) :
    partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
      = (P.rhoC i * α) y := by
  -- support (P.rhoC i) ⊆ (chartAt ℂ i.val).source (assembly layer).
  have hy_src : y ∈ (chartAt ℂ i.val).source :=
    support_rhoC_subset_chart_source P i hy
  -- Step 1: v_i =ᶠ[𝓝 y] chartPompeiuSolution (Sub-chip 5.4c-prep).
  have h_evEq :
      (localPompeiuSolutionGlobal P i α χ) =ᶠ[𝓝 y]
        (chartPompeiuSolution i P α) :=
    localPompeiuSolutionGlobal_eventuallyEq_chartPompeiuSolution_on_support_rhoC
      P i α χ hy
  -- Step 2: chart-anchored germ-bridge.
  have h_congr :
      partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
        = partialZBarManifoldAtChart i.val (chartPompeiuSolution i P α) y :=
    partialZBarManifoldAtChart_eventuallyEq_congr hy_src h_evEq
  rw [h_congr]
  -- Step 3: unfold and apply the chart-x_i view evaluation (Sub-chip 5.4c-final).
  show partialZBar ((chartPompeiuSolution i P α) ∘ (chartAt ℂ i.val).symm)
        ((chartAt ℂ i.val) y) = (P.rhoC i * α) y
  exact partialZBar_chartPompeiuSolution_chart_xi_symm_eq P i α h_α hy_src

end JacobianChallenge

end
