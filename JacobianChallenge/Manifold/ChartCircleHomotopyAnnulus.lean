/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchoredDischarge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chart-circle homotopy invariance over a regular annulus

Cauchy's theorem on an annulus, applied to the chart-anchored
log-derivative coefficient `logDiffCoeffAt f x`. If between two radii
`r₁ < r₂` the chart-pulled-back values of `logDiffCoeffAt f x` agree
with a single planar function `H : ℂ → ℂ` that is continuous on the
*closed* annulus `r₁ ≤ |z - z₀| ≤ r₂` and differentiable on the *open*
annulus `r₁ < |z - z₀| < r₂` (with `z₀ := (chartAt ℂ x) x`), then the
chart-anchored circle integrals at `r₁` and `r₂` agree:

```
chartCircleIntegralAnchored f x r₁ = chartCircleIntegralAnchored f x r₂.
```

This is the classical homotopy-invariance leg of the residue calculus:
moving the contour through a "regular" annulus (no zeros, no poles, no
chart-target failures) does not change the integral.

The proof reduces — via the de-bundled bridge
`chartCircleIntegralOfFun_eq_circleIntegral_of_eq` shipped in
`LogDiffAnchoredDischarge.lean` — to mathlib's annular Cauchy theorem
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
applied to `H` directly.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this is a pure addition.
* The annular invariance is proven via mathlib's
  `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
  (Cauchy-Goursat on an annulus).

## Layout

* Commit ZZ4.A — predicate `IsRegularOnAnnulus f x r₁ r₂`.
* Commit ZZ4.B — homotopy-invariance theorem
  `chartCircleIntegralAnchored_eq_of_regular_annulus`.
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Annular regularity predicate

`IsRegularOnAnnulus f x r₁ r₂` says that on the closed annulus of inner
radius `r₁` and outer radius `r₂` around the chart center
`z₀ := (chartAt ℂ x) x`, the chart-pulled-back values of
`logDiffCoeffAt f x` agree with a single planar function `H : ℂ → ℂ`
that is continuous on the *closed* annulus and differentiable on the
*open* annulus.

This is the mathematical content of "the chart-annulus contains no
zeros and no poles of `f`": under that classical hypothesis, `H` can
be taken to be the planar logarithmic derivative `(f̃)' / f̃` of
`f̃ := f.toFun ∘ (chartAt ℂ x).symm`, which is holomorphic on the
chart-annulus because `f̃` is and `f̃` is nonzero there.

Stated as a `Prop`-valued `def` (not `axiom`). -/
def IsRegularOnAnnulus
    (f : MeromorphicNonzero X) (x : X) (r₁ r₂ : ℝ) : Prop :=
  ∃ H : ℂ → ℂ,
    ContinuousOn H
      (Metric.closedBall ((chartAt ℂ x) x) r₂ \
        Metric.ball ((chartAt ℂ x) x) r₁) ∧
    DifferentiableOn ℂ H
      (Metric.ball ((chartAt ℂ x) x) r₂ \
        Metric.closedBall ((chartAt ℂ x) x) r₁) ∧
    (∀ θ : ℝ,
      logDiffCoeffAt f x ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r₁ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = H ((chartAt ℂ x) x + (r₁ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∧
    (∀ θ : ℝ,
      logDiffCoeffAt f x ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r₂ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = H ((chartAt ℂ x) x + (r₂ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-! ## ZZ4.B — chart-circle homotopy invariance over a regular annulus

The chart-anchored circle integrals at `r₁` and `r₂` agree, provided
`IsRegularOnAnnulus f x r₁ r₂` holds.

Proof: bridge each side to the planar circle integral of `H` via
`chartCircleIntegralOfFun_eq_circleIntegral_of_eq`, then apply
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
with the empty countable exceptional set. -/

theorem chartCircleIntegralAnchored_eq_of_regular_annulus
    (f : MeromorphicNonzero X) (x : X) (r₁ r₂ : ℝ)
    (h1 : 0 < r₁) (h12 : r₁ ≤ r₂)
    (hreg : IsRegularOnAnnulus f x r₁ r₂) :
    chartCircleIntegralAnchored f x r₁ =
      chartCircleIntegralAnchored f x r₂ := by
  obtain ⟨H, H_cont, H_diff, H_eq1, H_eq2⟩ := hreg
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- Helper: the chart-circle parameterisation matches `circleMap z₀ r`.
  have hsub : ∀ (r : ℝ) (θ : ℝ),
      circleMap z₀ r θ - z₀ = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro r θ
    rw [circleMap_sub_center, circleMap_zero, mul_comm (Complex.I) ((θ : ℂ))]
  have hmap : ∀ (r : ℝ) (θ : ℝ),
      circleMap z₀ r θ = z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro r θ
    have heq := hsub r θ
    linear_combination heq
  -- Bridge each chart-circle integral to a planar circle integral of H.
  have hbridge1 :
      chartCircleIntegralAnchored f x r₁ =
        (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(z₀, r₁), H z) := by
    unfold chartCircleIntegralAnchored
    refine chartCircleIntegralOfFun_eq_circleIntegral_of_eq
      (logDiffCoeffAt f x) x r₁ H ?_
    intro θ
    rw [H_eq1 θ, hmap r₁ θ]
  have hbridge2 :
      chartCircleIntegralAnchored f x r₂ =
        (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(z₀, r₂), H z) := by
    unfold chartCircleIntegralAnchored
    refine chartCircleIntegralOfFun_eq_circleIntegral_of_eq
      (logDiffCoeffAt f x) x r₂ H ?_
    intro θ
    rw [H_eq2 θ, hmap r₂ θ]
  -- Annular Cauchy: the two planar circle integrals agree.
  have hannulus :
      (∮ z in C(z₀, r₂), H z) = (∮ z in C(z₀, r₁), H z) := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      h1 h12 (s := (∅ : Set ℂ)) (Set.countable_empty) H_cont ?_
    intro z hz
    have hz' : z ∈ Metric.ball z₀ r₂ \ Metric.closedBall z₀ r₁ := hz.1
    exact (H_diff z hz').differentiableAt
      (IsOpen.mem_nhds (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall) hz')
  rw [hbridge1, hbridge2, hannulus]

end MeromorphicNonzero

end JacobianChallenge

end
