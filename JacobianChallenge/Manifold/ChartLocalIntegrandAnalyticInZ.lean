/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticOnIntervalIntegralParam
import JacobianChallenge.Manifold.ChartLocalIntegrandSmooth
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget

set_option linter.unusedSectionVars false

/-! # `AnalyticAt ℂ` in `z` of the chart-coord integrand

For an analytic `f : ℂ → ℂ` on a convex open set `S ∋ z₀` (e.g.,
`f = localCoeff om y` on `(chartAt ℂ y).target`), the chart-coord
integrand
`g(z, t) := f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t`
is `AnalyticAt ℂ` in `z` at each `z ∈ S` for every fixed `t : ℝ`.

The proof composes analyticity of `f` on `S` (hypothesis) with:
* `bumpedSegment z₀ · t` is **affine in `z`** (`(1-σ(t)) • z₀ + σ(t) • z`),
  hence `AnalyticAt ℂ` in `z`;
* `chartCoordVelocity z₀ · t = ((σ'(t):ℝ):ℂ) * (z - z₀)` is **affine
  in `z`**, hence `AnalyticAt ℂ` in `z`;
* `bumpedSegment z₀ z t ∈ S` by convexity (the bumped segment lies in
  `segment ℝ z₀ z ⊆ S`).

The product of two `AnalyticAt`s is `AnalyticAt`; composition with `f`
analytic at the image point closes.

## What this file ships

* `analyticAt_chartLocalIntegrand_in_z` — `AnalyticAt ℂ` in `z` of
  the chart-coord integrand at every `z ∈ S`, for each fixed `t : ℝ`.

This feeds the `HasDerivAt`-pointwise hypothesis of
`analyticOn_intervalIntegral_param` (chip 10) when we specialize to
the chartLocalPrimitive setting.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology
open Set

namespace JacobianChallenge

/-- **`AnalyticAt ℂ` in `z` of `bumpedSegment z₀ · t`** at every `z : ℂ`.

`bumpedSegment z₀ z t = (1 - σ t) • z₀ + σ t • z` is affine in `z`. -/
lemma analyticAt_bumpedSegment_in_z (z₀ : ℂ) (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun z' => bumpedSegment z₀ z' t) z := by
  unfold bumpedSegment
  -- (1 - σ(t)) • z₀ is a constant in z'; σ(t) • z' is ℂ-linear in z'.
  have h_const : AnalyticAt ℂ (fun _ : ℂ => (1 - Real.smoothTransition t) • z₀) z :=
    analyticAt_const
  have h_scale : AnalyticAt ℂ (fun z' : ℂ => (Real.smoothTransition t) • z') z := by
    -- Real • ℂ is the same as ℝ scalar mul; rewrite to ℂ-mult.
    have : (fun z' : ℂ => (Real.smoothTransition t) • z')
        = fun z' : ℂ => ((Real.smoothTransition t : ℝ) : ℂ) * z' := by
      funext z'; exact Complex.real_smul
    rw [this]
    exact analyticAt_const.mul analyticAt_id
  exact h_const.add h_scale

/-- **`AnalyticAt ℂ` in `z` of `chartCoordVelocity z₀ · t`** at every `z : ℂ`. -/
lemma analyticAt_chartCoordVelocity_in_z (z₀ : ℂ) (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun z' => chartCoordVelocity z₀ z' t) z := by
  unfold chartCoordVelocity
  -- ((σ'(t):ℝ):ℂ) * (z' - z₀) is ℂ-affine in z'.
  have h_sub : AnalyticAt ℂ (fun z' : ℂ => z' - z₀) z :=
    analyticAt_id.sub analyticAt_const
  exact analyticAt_const.mul h_sub

/-- **bumpedSegment image lies in `S`** under `Convex ℝ S` + `z₀, z ∈ S`. -/
lemma bumpedSegment_mem_of_convex
    {S : Set ℂ} (hS : Convex ℝ S) {z₀ z : ℂ} (hz₀ : z₀ ∈ S) (hz : z ∈ S) (t : ℝ) :
    bumpedSegment z₀ z t ∈ S :=
  hS.segment_subset hz₀ hz (bumpedSegment_mem_segment z₀ z t)

/-- **`AnalyticAt ℂ` in `z` of the chart-coord integrand** at every
`z ∈ S`, for each fixed `t : ℝ`.

For an `AnalyticOn ℂ f S` integrand-coefficient (e.g., `localCoeff om y`)
on a convex open set `S ⊆ ℂ` with `z₀ ∈ S`, the chart-coord integrand
`(fun z' => f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t)`
is `AnalyticAt ℂ` at every `z ∈ S`. -/
theorem analyticAt_chartLocalIntegrand_in_z
    {f : ℂ → ℂ} {S : Set ℂ} (hS : Convex ℝ S) (hS_open : IsOpen S)
    (hf : AnalyticOn ℂ f S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S)
    (t : ℝ) :
    AnalyticAt ℂ (fun z' => f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t) z := by
  -- f is analytic at bumpedSegment z₀ z t ∈ S (by convexity).
  have h_im_mem : bumpedSegment z₀ z t ∈ S :=
    bumpedSegment_mem_of_convex hS hz₀ hz t
  have hf_at : AnalyticAt ℂ f (bumpedSegment z₀ z t) :=
    hf.analyticAt (hS_open.mem_nhds h_im_mem)
  -- bumpedSegment z₀ · t is AnalyticAt at z.
  have h_bs : AnalyticAt ℂ (fun z' => bumpedSegment z₀ z' t) z :=
    analyticAt_bumpedSegment_in_z z₀ t z
  -- Composition: f ∘ bumpedSegment is AnalyticAt at z.
  have h_pos : AnalyticAt ℂ (fun z' => f (bumpedSegment z₀ z' t)) z := by
    have := AnalyticAt.comp (g := f) (f := fun z' => bumpedSegment z₀ z' t)
      (x := z) hf_at h_bs
    simpa [Function.comp] using this
  -- Velocity is AnalyticAt at z.
  have h_vel : AnalyticAt ℂ (fun z' => chartCoordVelocity z₀ z' t) z :=
    analyticAt_chartCoordVelocity_in_z z₀ t z
  -- Product is AnalyticAt.
  exact h_pos.mul h_vel

end JacobianChallenge

end
