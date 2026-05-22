/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BumpedSegmentParamSmooth

set_option linter.unusedSectionVars false

/-! # Joint `C^∞`-smoothness of the chart-coord integrand product

The chart-local primitive's interval-integral representation has the
form

  `F(z) = ∫_{0}^{1} f(bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t dt`

where `f : ℂ → ℂ` is the chart-coordinate coefficient of a holomorphic
1-form (i.e., `f = localCoeff om y` in the canonical-chart at `y`). The
integrand is *jointly smooth* in `(z, t)` on `S × ℝ` whenever `f` is
`ContDiffOn ℝ ∞` on a real-convex set `S ⊆ ℂ` containing both `z₀` and
the parametric input `z` (so that `bumpedSegment z₀ z t ∈ S` by
convexity for all `t : ℝ`).

This is the integrand-side joint smoothness needed by the parameter-
integral upgrade of `chartLocalPrimitive`-continuity to
`chartLocalPrimitive`-smoothness.

## What this file ships

* `contDiffOn_localCoeff_bumpedSegment_param` — joint smoothness on
  `S × Set.univ` of `(z, t) ↦ f (bumpedSegment z₀ z t)` under
  `ContDiffOn ℝ ∞ f S`, convexity of `S`, and `z₀ ∈ S`.
* `contDiffOn_chartLocalIntegrand_param` — joint smoothness on
  `S × Set.univ` of the full chart-coord integrand
  `(z, t) ↦ f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

/-- **Joint `ContDiffOn`-smoothness of `f ∘ bumpedSegment` on `S × univ`.**

If `f : ℂ → ℂ` is `ContDiffOn ℝ ∞` on a real-convex set `S ⊆ ℂ` with
`z₀ ∈ S`, then the map `(z, t) : ℂ × ℝ ↦ f (bumpedSegment z₀ z t)` is
`ContDiffOn ℝ ∞` on `S ×ˢ Set.univ`. Convexity of `S` and `z₀ ∈ S`
imply `bumpedSegment z₀ z t ∈ S` for all `t : ℝ` whenever `z ∈ S`,
because `bumpedSegment z₀ z t ∈ segment ℝ z₀ z ⊆ S`. -/
lemma contDiffOn_localCoeff_bumpedSegment_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hf : ContDiffOn ℝ ∞ f S) (hS : Convex ℝ S)
    (z₀ : ℂ) (hz₀ : z₀ ∈ S) :
    ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => f (bumpedSegment z₀ p.1 p.2))
      (S ×ˢ Set.univ) := by
  -- `(z, t) ↦ bumpedSegment z₀ z t` is `C^∞` on `ℂ × ℝ`.
  have h_bs_cd : ContDiff ℝ ∞ (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) :=
    contDiff_bumpedSegment_param z₀
  have h_bs_cdOn : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) (S ×ˢ Set.univ) :=
    h_bs_cd.contDiffOn
  -- The image of `S ×ˢ univ` under `bumpedSegment z₀ · ·` lies in `S`:
  -- for `(z, t) ∈ S × univ`, `bumpedSegment z₀ z t ∈ segment ℝ z₀ z ⊆ S`.
  have h_image : Set.MapsTo (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2)
      (S ×ˢ Set.univ) S := by
    rintro ⟨z, t⟩ ⟨hz, _⟩
    exact hS.segment_subset hz₀ hz (bumpedSegment_mem_segment z₀ z t)
  -- Compose: `ContDiffOn.comp` with the `MapsTo` hypothesis.
  exact hf.comp h_bs_cdOn h_image

/-- **Joint `ContDiffOn`-smoothness of the full chart-coord integrand
`(z, t) ↦ f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t` on
`S × univ`.**

Combines `contDiffOn_localCoeff_bumpedSegment_param` (smoothness of the
position-side factor) with `contDiff_chartCoordVelocity_param`
(smoothness of the velocity-side factor) and `ContDiffOn.mul`. -/
lemma contDiffOn_chartLocalIntegrand_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hf : ContDiffOn ℝ ∞ f S) (hS : Convex ℝ S)
    (z₀ : ℂ) (hz₀ : z₀ ∈ S) :
    ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ =>
        f (bumpedSegment z₀ p.1 p.2) * chartCoordVelocity z₀ p.1 p.2)
      (S ×ˢ Set.univ) := by
  have h_pos := contDiffOn_localCoeff_bumpedSegment_param hf hS z₀ hz₀
  have h_vel_cd : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => chartCoordVelocity z₀ p.1 p.2) :=
    contDiff_chartCoordVelocity_param z₀
  have h_vel : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => chartCoordVelocity z₀ p.1 p.2)
      (S ×ˢ Set.univ) :=
    h_vel_cd.contDiffOn
  exact h_pos.mul h_vel

end JacobianChallenge

end
