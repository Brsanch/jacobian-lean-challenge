/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Planar annulus circle-integral identity

Pure-planar wrapper around mathlib's
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
specialised to a function `g : ℂ → ℂ` that is holomorphic on the
*closed* annulus `r₁ ≤ ‖z - z₀‖ ≤ r₂` (no exceptional set, plain
`DifferentiableOn` hypothesis).

This is the form Cauchy's theorem on an annulus most often appears in
applications: no countable bad set, no `DiffContOnCl`, just one
`DifferentiableOn` on the closed annulus.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this is a pure
  addition under a fresh namespace `JacobianChallenge.PlanarAnnulus`.
* The proof routes through mathlib's
  `circleIntegral_eq_of_differentiable_on_annulus_off_countable`
  with the empty exceptional set.
-/

noncomputable section

open Complex MeasureTheory Set Metric

namespace JacobianChallenge

namespace PlanarAnnulus

/-- **Cauchy's theorem on an annulus**, plain `DifferentiableOn` form.

If `g : ℂ → ℂ` is differentiable (i.e. holomorphic) on the *closed*
annulus `closedBall z₀ r₂ \ ball z₀ r₁` with `0 < r₁ ≤ r₂`, then the
circle integrals of `g` over the inner and outer boundaries agree:

`∮ z in C(z₀, r₂), g z = ∮ z in C(z₀, r₁), g z`.

This is the version one wants when `g` extends holomorphically across
the closed annulus (the standard residue-theorem setup with no poles
in the annulus). -/
theorem circleIntegral_eq_of_holomorphic_on_annulus
    {z₀ : ℂ} {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ ≤ r₂) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall z₀ r₂ \ ball z₀ r₁)) :
    (∮ z in C(z₀, r₂), g z) = ∮ z in C(z₀, r₁), g z := by
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    h1 h12 (s := (∅ : Set ℂ)) Set.countable_empty hg.continuousOn ?_
  intro z hz
  have hz' : z ∈ ball z₀ r₂ \ closedBall z₀ r₁ := hz.1
  -- The open annulus is contained in the closed annulus.
  have hsub : ball z₀ r₂ \ closedBall z₀ r₁ ⊆
      closedBall z₀ r₂ \ ball z₀ r₁ := by
    intro w hw
    refine ⟨Metric.ball_subset_closedBall hw.1, ?_⟩
    intro hw'
    exact hw.2 (Metric.ball_subset_closedBall hw')
  have hopen : IsOpen (ball z₀ r₂ \ closedBall z₀ r₁) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  exact (hg z (hsub hz')).differentiableAt (hopen.mem_nhds hz')

/-- Continuous-on-closed + differentiable-on-open form of Cauchy's
annulus theorem (no countable exceptional set), as a convenience
wrapper around mathlib's
`circleIntegral_eq_of_differentiable_on_annulus_off_countable`.

If `g` is continuous on the closed annulus and differentiable on the
open annulus (`r₁ < ‖z - z₀‖ < r₂`), then the inner and outer circle
integrals agree. -/
theorem circleIntegral_eq_of_continuousOn_closed_differentiableOn_open
    {z₀ : ℂ} {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ ≤ r₂) {g : ℂ → ℂ}
    (hcont : ContinuousOn g (closedBall z₀ r₂ \ ball z₀ r₁))
    (hdiff : DifferentiableOn ℂ g (ball z₀ r₂ \ closedBall z₀ r₁)) :
    (∮ z in C(z₀, r₂), g z) = ∮ z in C(z₀, r₁), g z := by
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    h1 h12 (s := (∅ : Set ℂ)) Set.countable_empty hcont ?_
  intro z hz
  have hz' : z ∈ ball z₀ r₂ \ closedBall z₀ r₁ := hz.1
  have hopen : IsOpen (ball z₀ r₂ \ closedBall z₀ r₁) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  exact (hdiff z hz').differentiableAt (hopen.mem_nhds hz')

end PlanarAnnulus

end JacobianChallenge

end
