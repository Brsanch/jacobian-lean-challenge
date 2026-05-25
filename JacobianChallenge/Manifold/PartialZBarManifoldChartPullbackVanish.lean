/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBarManifold
import JacobianChallenge.Manifold.PartialZBarChainRule
import JacobianChallenge.Manifold.MeromorphicAt

set_option linter.unusedSectionVars false

/-! # Chart-pullback transfer of `partialZBar` vanishing

A complex 1-manifold's `partialZBarManifold f y` is defined via the
canonical chart `chartAt ℂ y`. For the upcoming Chip 2c-Final closure
(Forster §16.9 cutoff + correction → `ExistsSimplePoleGermAtSomePoint X`),
we need to discharge analyticity hypotheses for the consolidator
`existsSimplePoleGermAtSomePoint_of_chartPullback_data` at points `x ≠ p`
using **any** chart at `x` — typically the canonical `chartAt ℂ x`.

The wedge: `partialZBarManifold f y = 0` gives `partialZBar` vanishing in
the *chart-y* representation, but the consolidator needs vanishing in
the *chart-x* representation when computing CR-converse analyticity at
points `y` near `x` (with `chart_y` possibly different from `chart_x`).

This file ships the unconditional bridge: under the holomorphic
chart-transition `(chartAt ℂ y) ∘ (chartAt ℂ x).symm` (automatic via
`IsManifold 𝓘(ℂ, ℂ) ω X`), the chain rule for `partialZBar`
(`partialZBar_comp_of_differentiableAt`) multiplies the chart-y
representation's `partialZBar` by `conj(deriv (transition))` — and `0`
times anything is `0`. So vanishing transfers from the chart-y
representation to the chart-x representation pointwise.

## What this ships

* `partialZBarChartPullback_eq_zero_of_partialZBarManifold_zero` —
  if `y ∈ (chartAt ℂ x).source`, the manifold-side `partialZBar` of `f`
  at `y` vanishes, and the chart-y pullback of `f` is `ℝ`-differentiable
  at `(chartAt ℂ y) y`, then the chart-x pullback of `f` has vanishing
  `partialZBar` at `(chartAt ℂ x) y`.

This is the chart-locality bridge needed for H2 of the Chip-2
consolidator on arbitrary `X`. It removes the need for a
`LocallyConstantChartAt X` typeclass at the H2 step — chart-transition
analyticity does the work.

No `sorry`, no `axiom`. -/

noncomputable section

namespace JacobianChallenge

open scoped Manifold ContDiff Topology
open Complex Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chart-pullback vanishing of `partialZBar` transfers across chart
transitions.**

If `y ∈ (chartAt ℂ x).source` (so chart_x covers `y` too) and the
manifold-side `partialZBarManifold f y` vanishes (i.e., chart-y view of
`∂̄ f` at `chart_y y` is zero), then the chart-x view of `∂̄ f` at
`chart_x y` is also zero.

The `ℝ`-differentiability hypothesis on `f ∘ chart_y.symm` is needed to
apply the chain rule for `partialZBar`; the chart transition
`chart_y ∘ chart_x.symm` is automatically ℂ-analytic (from
`IsManifold 𝓘(ℂ, ℂ) ω X`).

This bridge is unconditional on `X` — no `LocallyConstantChartAt`-style
typeclass required. -/
lemma partialZBarChartPullback_eq_zero_of_partialZBarManifold_zero
    {f : X → ℂ} {x y : X}
    (h_y_in_xsrc : y ∈ (chartAt ℂ x).source)
    (h_man : partialZBarManifold f y = 0)
    (h_f_diff_y : DifferentiableAt ℝ (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)) :
    partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) = 0 := by
  -- Atlas memberships and source memberships.
  have h_x_atlas : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have h_y_atlas : chartAt ℂ y ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have h_y_in_ysrc : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  -- Chart transition `(chartAt ℂ y) ∘ (chartAt ℂ x).symm` is ℂ-analytic at `(chart_x y)`.
  have h_an_trans : AnalyticAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) y) :=
    analyticAt_chart_transition_of_isManifold h_x_atlas h_y_atlas h_y_in_xsrc h_y_in_ysrc
  have h_Φ_diff : DifferentiableAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) y) := h_an_trans.differentiableAt
  -- Transition's value at chart_x y equals chart_y y (via chart_x.left_inv).
  have h_trans_apply : ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = (chartAt ℂ y) y := by
    change (chartAt ℂ y) ((chartAt ℂ x).symm ((chartAt ℂ x) y))
        = (chartAt ℂ y) y
    rw [(chartAt ℂ x).left_inv h_y_in_xsrc]
  -- Build the eventual-equality nbhd around `(chartAt ℂ x) y` in `chartAt ℂ x).target`
  -- where `chart_x.symm w ∈ (chartAt ℂ y).source` (so `chart_y` can act on it).
  have h_pre_open : IsOpen ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ y).open_source
  have h_x_target_mem : (chartAt ℂ x) y ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source h_y_in_xsrc
  have h_y_in_pre : (chartAt ℂ x) y ∈ (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := by
    refine ⟨h_x_target_mem, ?_⟩
    change (chartAt ℂ x).symm ((chartAt ℂ x) y) ∈ (chartAt ℂ y).source
    rw [(chartAt ℂ x).left_inv h_y_in_xsrc]; exact h_y_in_ysrc
  -- Eventual equality: `f ∘ chart_x.symm` agrees with
  -- `(f ∘ chart_y.symm) ∘ (chart_y ∘ chart_x.symm)` on the open nbhd where
  -- `chart_x.symm w ∈ chart_y.source` (using `chart_y.left_inv`).
  have h_evEq :
      (f ∘ (chartAt ℂ x).symm)
        =ᶠ[nhds ((chartAt ℂ x) y)]
        ((f ∘ (chartAt ℂ y).symm) ∘ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_pre_open.mem_nhds h_y_in_pre, ?_⟩
    intro w hw
    obtain ⟨_hw_tgt, hw_pre⟩ := hw
    -- hw_pre: chart_x.symm w ∈ chart_y.source. So chart_y.left_inv applies.
    change f ((chartAt ℂ x).symm w)
        = f ((chartAt ℂ y).symm ((chartAt ℂ y) ((chartAt ℂ x).symm w)))
    rw [(chartAt ℂ y).left_inv hw_pre]
  -- `partialZBar` is local (defined via `fderiv`), so congruence under eventual equality.
  have h_pZ_congr : partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = partialZBar ((f ∘ (chartAt ℂ y).symm) ∘ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm))
          ((chartAt ℂ x) y) := by
    unfold partialZBar
    rw [Filter.EventuallyEq.fderiv_eq h_evEq]
  rw [h_pZ_congr]
  -- Apply the chain rule for `partialZBar`.
  -- Requires `f ∘ chart_y.symm` `ℝ`-differentiable at `(chart_y ∘ chart_x.symm) (chart_x y)`.
  have h_diff_at_trans :
      DifferentiableAt ℝ (f ∘ (chartAt ℂ y).symm)
        (((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) := by
    rw [h_trans_apply]; exact h_f_diff_y
  rw [partialZBar_comp_of_differentiableAt h_diff_at_trans h_Φ_diff]
  -- Goal: partialZBar (f ∘ chart_y.symm) (chart_y y) * conj(...) = 0.
  rw [h_trans_apply]
  -- The first factor IS `partialZBarManifold f y` by definition.
  have h_first_factor : partialZBar (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
      = partialZBarManifold f y := rfl
  rw [h_first_factor, h_man]
  ring

end JacobianChallenge

end
