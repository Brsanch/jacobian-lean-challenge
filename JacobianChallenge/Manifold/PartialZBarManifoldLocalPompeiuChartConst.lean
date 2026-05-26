/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionAtChartIdentity
import JacobianChallenge.Manifold.GlobalSolutionCandidatePartialZBar
import JacobianChallenge.Manifold.ForsterCutoffPoleConstruction

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-d — canonical-chart factor-free per-i recovery

Sub-chip 5.5b gave the **chart-anchored** factor-free identity
```
partialZBarManifoldAtChart i.val v_i y = (P.rhoC i * α) y
```
on `support (P.rhoC i)`. Sub-chip 5.5a's transfer lemma relates the
chart-anchored operator to the canonical-chart `partialZBarManifold`
via a conjugate-derivative transition factor.

Under the global hypothesis `∀ p, ChartAtConstantOnSource p`
(`chartAt ℂ` is locally constant on each chart source — the same
chart-locality property the Forster §16.9 cutoff already takes,
extended to every point of `X`), the transition derivative collapses
to `1` whenever `y ∈ (chartAt ℂ i.val).source`, since
`chartAt ℂ y = chartAt ℂ i.val` there. This drops the chart-anchored
identity directly to a **canonical-chart** identity:

```
partialZBarManifold v_i y = (P.rhoC i * α) y
```

on `support (P.rhoC i)`, with no transition factor.

This is the factor-free per-i recovery in the canonical chart-y
view. Combined with the assembly layer's distributivity
`partialZBarManifold (Σ_i v_i) y = Σ_i partialZBarManifold v_i y` and
the trivial-vanishing case `partialZBarManifold v_i y = 0` off
`tsupport (χ_i)`, the next sub-chip (5.5c-I-e) attempts the global
assembly under the same chart-locality hypothesis.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Function

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
  {cover : FiniteChartCover X}

/-! ## Transition derivative collapses to 1 under chart-const -/

/-- Under `ChartAtConstantOnSource i.val`, for `y ∈ chart_{i.val}.source`,
`chart_y = chart_{i.val}`, so the transition derivative
`deriv(chart_y ∘ chart_{i.val}.symm)` at `chart_{i.val}(y)` equals
`deriv id = 1`. -/
lemma deriv_chart_transition_eq_one_under_chart_const
    {i : X} {y : X}
    (h_chart_i : JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource i)
    (hy : y ∈ (chartAt ℂ i).source) :
    deriv ((chartAt ℂ y) ∘ (chartAt ℂ i).symm) ((chartAt ℂ i) y) = 1 := by
  -- chart_y = chart_i by chart-const.
  have h_eq : chartAt ℂ y = chartAt ℂ i := h_chart_i y hy
  rw [h_eq]
  -- chart_i ∘ chart_i.symm = id on chart_i.target; differentiate eventually-equal.
  have h_y_tgt : (chartAt ℂ i) y ∈ (chartAt ℂ i).target :=
    (chartAt ℂ i).map_source hy
  have h_open : IsOpen (chartAt ℂ i).target := (chartAt ℂ i).open_target
  have h_evEq :
      ((chartAt ℂ i) ∘ (chartAt ℂ i).symm) =ᶠ[𝓝 ((chartAt ℂ i) y)] id := by
    filter_upwards [h_open.mem_nhds h_y_tgt] with w hw
    show (chartAt ℂ i) ((chartAt ℂ i).symm w) = w
    exact (chartAt ℂ i).right_inv hw
  rw [Filter.EventuallyEq.deriv_eq h_evEq, deriv_id]

/-! ## Canonical-chart factor-free per-i recovery -/

/-- **Factor-free per-i recovery in the canonical chart.** Under the
global hypothesis `∀ p, ChartAtConstantOnSource p`, for each
`i ∈ cover.basePoints` and each `y ∈ support (P.rhoC i)`:
```
partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y
  = (P.rhoC i * α) y.
```
This is Sub-chip 5.5b's chart-anchored identity transported to the
canonical chart-`y` frame via the chart-const collapse of the
transition derivative. -/
theorem partialZBarManifold_localPompeiuSolutionGlobal_eq_rhoC_mul_alpha_under_chart_const
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    {y : X} (hy : y ∈ Function.support (P.rhoC i)) :
    partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y
      = (P.rhoC i * α) y := by
  -- Step 1: support (P.rhoC i) ⊆ (chartAt ℂ i.val).source.
  have hy_src : y ∈ (chartAt ℂ i.val).source :=
    support_rhoC_subset_chart_source P i hy
  -- Step 2: Sub-chip 5.5b — chart-anchored identity.
  have h_anchored :
      partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
        = (P.rhoC i * α) y :=
    partialZBarManifoldAtChart_localPompeiuSolutionGlobal_eq_rhoC_mul_alpha_on_support_rhoC
      P i α h_α χ hy
  -- Step 3: differentiability of v_i ∘ chart_y.symm at chart_y y.
  --   localPompeiuSolutionGlobal is ContMDiff (Sub-chip 5.4b); apply
  --   `differentiableAt_extChartAt_pullback_of_contMDiff` at x = y, point y.
  have h_v_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (localPompeiuSolutionGlobal P i α χ) :=
    contMDiff_localPompeiuSolutionGlobal P i α h_α χ
  have h_y_in_y : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have h_diff_v :
      DifferentiableAt ℝ ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) := by
    -- Use extChartAt = chartAt definitionally for 𝓘(ℂ, ℂ).
    have h := differentiableAt_extChartAt_pullback_of_contMDiff
      (u := localPompeiuSolutionGlobal P i α χ) h_v_smooth y y h_y_in_y
    -- (extChartAt 𝓘(ℂ, ℂ) y) y = (chartAt ℂ y) y definitionally.
    exact h
  -- Step 4: 5.5a transfer.
  have h_bridge :
      partialZBar ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ i.val).symm)
          ((chartAt ℂ i.val) y)
        = partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y *
            (starRingEnd ℂ)
              (deriv ((chartAt ℂ y) ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y)) :=
    JacobianChallenge.PompeiuKernel.partialZBar_chart_x_eq_manifold_mul_transition
      (f := localPompeiuSolutionGlobal P i α χ) (x := i.val) (y := y)
      hy_src h_diff_v
  -- LHS of h_bridge is `partialZBarManifoldAtChart i.val (...) y` by definition.
  have h_transfer :
      partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
        = partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y *
            (starRingEnd ℂ)
              (deriv ((chartAt ℂ y) ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y)) :=
    h_bridge
  -- Step 5: deriv = 1 under chart-const.
  have h_deriv :
      deriv ((chartAt ℂ y) ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y) = 1 :=
    deriv_chart_transition_eq_one_under_chart_const (h_chart i.val) hy_src
  rw [h_deriv, show (starRingEnd ℂ) 1 = 1 from map_one _, mul_one] at h_transfer
  -- Step 6: combine h_anchored = (LHS of h_transfer) and h_transfer = canonical view.
  rw [h_transfer] at h_anchored
  exact h_anchored

end JacobianChallenge

end
