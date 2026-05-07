/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalKFoldMultiplicityUnconditional
import JacobianChallenge.Manifold.LocalMultiplicityChartPullback
import JacobianChallenge.Manifold.PoleExtensionFibres
import JacobianChallenge.Manifold.RiemannSphere

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `k`-fold local multiplicity — chart-pullback lift to `ftilde : X → S²`

This file generalises `localMultiplicityOnManifold_preimage_card_one` (ZZ79,
`Manifold/LocalMultiplicityChartPullback.lean`) from the planar `k = 1` case
to general `k ≥ 1`, by composing ZZ89's unconditional planar `k`-fold count
`localKFoldMultiplicity_preimage_card_of_substitution`
(`Manifold/LocalKFoldMultiplicityUnconditional.lean`) with the chart pullback
`chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm`.

The shape is identical to ZZ79: the manifold-level preimage problem
`{x ∈ U | ftilde x = y}` is reduced to the planar problem
`{z ∈ V | (chartN ∘ ftilde ∘ c.symm) z = chartN y}`, and the planar problem
is supplied as a `KthRootSubstitution` bundle of order `k`.

## What this file ships

1. **`LocalKFoldMultiplicityOnManifoldHypothesis ftilde x₀ k`** — same shape
   as `LocalMultiplicityOnManifoldHypothesis` but parametric in `k`. The
   bundle stores the planar `KthRootSubstitution` of order `k`.

2. **`localKFoldMultiplicityOnManifold_preimage_card`** — the manifold-level
   `k`-fold count over the chart-pullback equation: for every value
   `w ∈ Metric.ball (chartN (ftilde x₀)) δ` with `w ≠ chartN (ftilde x₀)`, the
   chart-source preimage has cardinality exactly `k`.

3. **`localKFoldMultiplicityOnManifoldHypothesis_of_chartPullbackFactorization`**
   — convenience: build the bundle from a planar local factorization
   `g(z) - w₀ = (z - x₀)^k · u(z)` on the chart pullback.

The genuine manifold-level count `{x ∈ U | ftilde x = y}.ncard = k` follows
from (2) by the chart bijection `c.symm` once a stays-finite hypothesis on
`ftilde` near `x₀` is supplied — exactly as in ZZ79's header note. This
file inherits that residual.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology Manifold ContDiff
open Set Filter Metric OnePoint

namespace JacobianChallenge
namespace Manifold

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Tier-2 hypothesis bundle for manifold-side `k`-fold local multiplicity.**

For a map `ftilde : X → RiemannSphere`, a basepoint `x₀ : X`, and `k : ℕ`,
this bundle states that the chart pullback
`chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm`
has a planar `KthRootSubstitution` of order `k` at the chart image
`(chartAt ℂ x₀) x₀`, computing `chartN (ftilde x₀)`. This is the parametric
generalisation of `LocalMultiplicityOnManifoldHypothesis`; the `k = 1`
specialisation recovers ZZ79's bundle data. -/
structure LocalKFoldMultiplicityOnManifoldHypothesis
    (ftilde : X → RiemannSphere) (x₀ : X) (k : ℕ) : Prop where
  /-- The basepoint is a finite value of `ftilde` (so `chartN` is the right
  codomain chart). -/
  finite_value : ftilde x₀ ≠ (∞ : RiemannSphere)
  /-- The chart-pullback representative satisfies the planar
  `KthRootSubstitution` bundle of order `k`. -/
  planar_substitution :
    KthRootSubstitution
      (RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀)
      (RiemannSphere.chartN (ftilde x₀))
      k

/-- **Build the manifold bundle from a planar local factorization.**

If the chart pullback
`g := chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm` admits a local analytic
factorization `g(z) - w₀ = (z - x₀_chart)^k · u(z)` with `u` analytic and
non-vanishing at `x₀_chart`, and `ftilde x₀ ≠ ∞`, then the manifold-level
`LocalKFoldMultiplicityOnManifoldHypothesis ftilde x₀ k` holds. -/
theorem localKFoldMultiplicityOnManifoldHypothesis_of_chartPullbackFactorization
    {ftilde : X → RiemannSphere} {x₀ : X} {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (h_finite : ftilde x₀ ≠ (∞ : RiemannSphere))
    {u : ℂ → ℂ}
    (hu_an : AnalyticOnNhd ℂ u
      (Metric.closedBall ((chartAt ℂ x₀) x₀) R))
    (hu_x₀ : u ((chartAt ℂ x₀) x₀) ≠ 0)
    (hfact : ∀ z ∈ Metric.closedBall ((chartAt ℂ x₀) x₀) R,
        (RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm) z
          - RiemannSphere.chartN (ftilde x₀)
          = (z - (chartAt ℂ x₀) x₀) ^ k * u z) :
    LocalKFoldMultiplicityOnManifoldHypothesis ftilde x₀ k := by
  refine ⟨h_finite, ?_⟩
  exact kthRootSubstitution_of_localFactorization
          (g := RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm)
          (x₀ := (chartAt ℂ x₀) x₀)
          (w₀ := RiemannSphere.chartN (ftilde x₀))
          (k := k)
          hR hk hu_an hu_x₀ hfact

/-- **`k`-fold chart-pullback preimage count on the manifold.**

Given `LocalKFoldMultiplicityOnManifoldHypothesis ftilde x₀ k` with `k ≥ 1`,
there exist `ε > 0` and `δ > 0` such that for every chart-image value
`w ∈ Metric.ball (chartN (ftilde x₀)) δ` with `w ≠ chartN (ftilde x₀)`, the
chart-pullback preimage set has cardinality exactly `k`:
`{z ∈ ball ((chartAt ℂ x₀) x₀) ε | (chartN ∘ ftilde ∘ c.symm) z = w}.ncard = k`.

This is the parametric generalisation of `localMultiplicityOnManifold_preimage_card_one`
(ZZ79). The genuine manifold-level count `{x | ftilde x = y}.ncard = k` follows
by chart bijectivity once a stays-finite hypothesis on `ftilde` near `x₀` is
supplied (see the file header). -/
theorem localKFoldMultiplicityOnManifold_preimage_card
    {ftilde : X → RiemannSphere} {x₀ : X} {k : ℕ}
    (hk : 1 ≤ k)
    (h : LocalKFoldMultiplicityOnManifoldHypothesis ftilde x₀ k) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (RiemannSphere.chartN (ftilde x₀)) δ,
        w ≠ RiemannSphere.chartN (ftilde x₀) →
        ({z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ε |
            (RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm) z = w}
          : Set ℂ).ncard = k := by
  obtain ⟨_h_finite, hsub⟩ := h
  -- The chart pullback `g` evaluated at `(chartAt ℂ x₀) x₀` recovers
  -- `chartN (ftilde x₀)` because `c.symm (c x₀) = x₀`.
  have h_base : (RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) = RiemannSphere.chartN (ftilde x₀) := by
    have hx₀_src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
    show RiemannSphere.chartN
        (ftilde ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀))) =
      RiemannSphere.chartN (ftilde x₀)
    rw [(chartAt ℂ x₀).left_inv hx₀_src]
  -- Apply ZZ89's planar `k`-fold count to the chart pullback.
  have h_planar :=
    localKFoldMultiplicity_preimage_card_of_substitution
      (g := RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm)
      (x₀ := (chartAt ℂ x₀) x₀)
      (w₀ := RiemannSphere.chartN (ftilde x₀))
      (k := k) hk hsub h_base
  obtain ⟨ε, hε_pos, δ, hδ_pos, h_count⟩ := h_planar
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  -- ZZ89 phrases the ball/ne against `g x₀_chart`; rewrite via `h_base`.
  have hw_ball' : w ∈ Metric.ball
      ((RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm)
        ((chartAt ℂ x₀) x₀)) δ := by
    rw [h_base]; exact hw_ball
  have hw_ne' : w ≠ (RiemannSphere.chartN ∘ ftilde ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) := by
    rw [h_base]; exact hw_ne
  exact h_count w hw_ball' hw_ne'

end Manifold
end JacobianChallenge

end
