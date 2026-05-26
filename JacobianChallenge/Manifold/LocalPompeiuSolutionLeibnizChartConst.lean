/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionLeibniz
import JacobianChallenge.Manifold.PartialZBarManifoldLocalPompeiuChartConst
import JacobianChallenge.Manifold.ForsterCutoffPoleConstruction

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-g — canonical-chart Leibniz decomposition under chart-const

Sub-chip 5.5c-I-f gave the chart-anchored Leibniz decomposition

```
partialZBarManifoldAtChart i.val v_i y
  = partialZBarManifoldAtChart i.val (χ : ℂ) y · K_i(chart_{i.val} y)
  + χ(y) · (P.rhoC i * α)(y)
```

for `y ∈ (chartAt ℂ i.val).source`.

Under the global hypothesis `∀ p, ChartAtConstantOnSource p`, the
chart-anchored operator at anchor `i.val` coincides with the
canonical-chart operator `partialZBarManifold` for any
`y ∈ chart_{i.val}.source` (since `chart_y = chart_{i.val}` there,
so the transition derivative collapses to `1`). This sub-chip
transports the Leibniz decomposition to the canonical chart-y view:

```
partialZBarManifold v_i y
  = partialZBarManifold (χ : ℂ) y · K_i(chart_{i.val} y)
  + χ(y) · (P.rhoC i * α)(y).
```

On `support (P.rhoC i)` (where `χ ≡ 1`, so `partialZBarManifold (1 : ℂ) y
= 0`), this collapses to Sub-chip 5.5c-I-d's identity
`partialZBarManifold v_i y = (P.rhoC i * α)(y)`. On the outer ring
`tsupport χ \ support (P.rhoC i)` (where `(P.rhoC i * α)(y) = 0`),
it collapses to the **cutoff-derivative leakage**
`partialZBarManifold (χ : ℂ) y · K_i(chart_{i.val} y)` — the explicit
remaining analytic content.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Function
open JacobianChallenge.PompeiuKernel

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
  {cover : FiniteChartCover X}

/-! ## Helper: transfer `partialZBarManifoldAtChart` to `partialZBarManifold` under chart-const -/

/-- **Chart-anchored = canonical-chart under chart-const.** For any
`f : X → ℂ` with chart-y-pullback differentiable at `chart_y y`, and
`y ∈ chart_{i.val}.source`, under `ChartAtConstantOnSource i.val`:
```
partialZBarManifoldAtChart i.val f y = partialZBarManifold f y.
```
The chart-transition derivative is `1` (deriv id), conj 1 = 1. -/
lemma partialZBarManifoldAtChart_eq_partialZBarManifold_under_chart_const
    {i : X} {f : X → ℂ}
    (h_chart_i : JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource i)
    {y : X} (hy : y ∈ (chartAt ℂ i).source)
    (h_f_diff : DifferentiableAt ℝ (f ∘ (chartAt ℂ y).symm)
                  ((chartAt ℂ y) y)) :
    partialZBarManifoldAtChart i f y = partialZBarManifold f y := by
  have h_bridge :=
    JacobianChallenge.PompeiuKernel.partialZBar_chart_x_eq_manifold_mul_transition
      (f := f) (x := i) (y := y) hy h_f_diff
  -- h_bridge : partialZBar(f ∘ chart_i.symm)(chart_i y) =
  --            partialZBarManifold f y * conj(deriv(chart_y ∘ chart_i.symm)(chart_i y))
  -- LHS = partialZBarManifoldAtChart i f y by definition.
  -- Deriv = 1 under chart-const.
  have h_deriv :
      deriv ((chartAt ℂ y) ∘ (chartAt ℂ i).symm) ((chartAt ℂ i) y) = 1 :=
    deriv_chart_transition_eq_one_under_chart_const h_chart_i hy
  rw [h_deriv, show (starRingEnd ℂ) 1 = 1 from map_one _, mul_one] at h_bridge
  -- h_bridge : partialZBarManifoldAtChart i f y = partialZBarManifold f y.
  exact h_bridge

/-! ## Canonical-chart Leibniz decomposition -/

/-- **Canonical-chart Leibniz decomposition of `v_i` under chart-const.**
For `y ∈ (chartAt ℂ i.val).source` under global
`∀ p, ChartAtConstantOnSource p`:
```
partialZBarManifold v_i y
  = partialZBarManifold (χ.toFun · : X → ℂ) y · K_i(chart_{i.val} y)
  + ((χ.toFun y : ℝ) : ℂ) · (P.rhoC i * α)(y).
```
Lifts Sub-chip 5.5c-I-f via the chart-anchored / canonical-chart
collapse under chart-const. -/
theorem partialZBarManifold_localPompeiuSolutionGlobal_leibniz_under_chart_const
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y
      = partialZBarManifold (fun z : X => ((χ.toFun z : ℝ) : ℂ)) y *
          pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
            ((chartAt ℂ i.val) y)
        + ((χ.toFun y : ℝ) : ℂ) * (P.rhoC i * α) y := by
  -- Step 1: differentiability of v_i ∘ chart_y.symm at chart_y y.
  have h_v_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (localPompeiuSolutionGlobal P i α χ) :=
    contMDiff_localPompeiuSolutionGlobal P i α h_α χ
  have h_y_in_y : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have h_diff_v :
      DifferentiableAt ℝ
        ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) :=
    differentiableAt_extChartAt_pullback_of_contMDiff
      (u := localPompeiuSolutionGlobal P i α χ) h_v_smooth y y h_y_in_y
  -- Step 2: differentiability of (χ.toFun · : ℂ) ∘ chart_y.symm at chart_y y.
  have h_χC_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : X => ((χ.toFun z : ℝ) : ℂ)) := by
    have h_χ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ.toFun := χ.smooth
    have h_cast : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
        (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contMDiff
    exact h_cast.comp h_χ
  have h_diff_χC :
      DifferentiableAt ℝ
        ((fun z : X => ((χ.toFun z : ℝ) : ℂ)) ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) :=
    differentiableAt_extChartAt_pullback_of_contMDiff
      (u := fun z : X => ((χ.toFun z : ℝ) : ℂ)) h_χC_smooth y y h_y_in_y
  -- Step 3: chart-anchored Leibniz from 5.5c-I-f.
  have h_leibniz_anchored :=
    partialZBarManifoldAtChart_localPompeiuSolutionGlobal_leibniz P i h_α χ hy
  -- Step 4: transfer chart-anchored ↔ canonical-chart for v_i and χcast under chart-const.
  have h_transfer_v :
      partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
        = partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y :=
    partialZBarManifoldAtChart_eq_partialZBarManifold_under_chart_const
      (h_chart i.val) hy h_diff_v
  have h_transfer_χC :
      partialZBarManifoldAtChart i.val (fun z : X => ((χ.toFun z : ℝ) : ℂ)) y
        = partialZBarManifold (fun z : X => ((χ.toFun z : ℝ) : ℂ)) y :=
    partialZBarManifoldAtChart_eq_partialZBarManifold_under_chart_const
      (h_chart i.val) hy h_diff_χC
  rw [h_transfer_v, h_transfer_χC] at h_leibniz_anchored
  exact h_leibniz_anchored

end JacobianChallenge

end
