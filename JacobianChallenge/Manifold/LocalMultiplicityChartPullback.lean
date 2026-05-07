/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalKFoldMultiplicity
import JacobianChallenge.Manifold.PoleExtensionFibres
import JacobianChallenge.Manifold.RiemannSphere

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local multiplicity invariance — chart-pullback lift to `f̃ : X → S²`

This file lifts the planar `k = 1` local-multiplicity invariance of ZZ74
(`localMultiplicityOne_preimage_card`) and the `k`-th root substitution
bundle of ZZ75 (`KthRootSubstitution`,
`localKFoldMultiplicity_preimage_card_of_substitution_one`) from a planar
analytic map `g : ℂ → ℂ` to a map

  `f̃ : X → RiemannSphere`

on a charted complex 1-manifold `X`. The strategy is **chart pullback**:
a chart `c := chartAt ℂ x₀` on the source side and the codomain chart
`chartN : OpenPartialHomeomorph RiemannSphere ℂ` on the target side
together turn the manifold-level preimage-count problem
`{x ∈ U | f̃ x = y}` into the planar problem
`{z ∈ V | (chartN ∘ f̃ ∘ c.symm) z = chartN y}` for finite-value targets
`y ≠ ∞`.

## What this file ships (Tier-2 reduction)

The fully unconditional manifold lift would route manifold-level
smoothness `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f̃` into the chart pullback being
analytic, plus a continuity argument forcing `f̃` into `chartN.source`
near `x₀`. The first ingredient is the existing bridge
`contMDiffAt_omega_analyticAt_chart_pullback`
(`Manifold/ContMDiffOmegaAnalytic.lean`); the second is automatic from
continuity of `f̃` at `x₀` with `f̃ x₀ ≠ ∞`. Both prerequisites are
not yet wired here because `MeromorphicNonzero.toRiemannSphere` is
`ContMDiff` only conditionally on the named-only hypothesis
`toRiemannSphere_contMDiff_statement`
(`Manifold/MeromorphicExtension.lean`).

We therefore ship a **Tier-2 hypothesis bundle** plus an unconditional
ε–δ count for the chart-pullback equation:

1. **`LocalMultiplicityOnManifoldHypothesis f̃ x₀ k`** — a hypothesis
   bundle stating that the chart-pullback
   `chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm` has a planar `KthRootSubstitution`
   at `(chartAt ℂ x₀) x₀`.

2. **`localMultiplicityOnManifold_preimage_card_one`** — the manifold-level
   `k = 1` count over the **chart pullback equation**: for every value
   `w ∈ Metric.ball (chartN (f̃ x₀)) δ` with `w ≠ chartN (f̃ x₀)`, the
   chart-source preimage `{z ∈ ball ((chartAt ℂ x₀) x₀) ε |
   (chartN ∘ f̃ ∘ c.symm) z = w}` has cardinality exactly `1`.

3. **`localMultiplicityOnManifoldHypothesis_one_of_chartPullbackAnalytic`**
   — convenience: build the bundle from a planar `k = 1` hypothesis
   on the chart pullback (analytic on a closed disc + non-zero
   derivative), via ZZ75's
   `kthRootSubstitution_of_localMultiplicityOne`.

The remaining "genuine" count `{x ∈ U | f̃ x = y}.ncard = 1` follows from
(2) by the chart bijection `c.symm`, **once** a stays-finite hypothesis
on `f̃` (∃ ρ > 0, ∀ x ∈ chart-source-disc, `f̃ x ≠ ∞`) is supplied with
ρ matching the ε of (2). Since the count is purely chart-pullback in
its current form, this last absorption is left to consumers (it is a
two-line bookkeeping argument once continuity of `f̃` at `x₀` is in
hand — see the file header note).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology Manifold ContDiff
open Set Filter Metric OnePoint

namespace JacobianChallenge
namespace Manifold

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Tier-2 hypothesis bundle for manifold-side local multiplicity.**

For a map `f̃ : X → RiemannSphere`, a basepoint `x₀ : X`, and `k : ℕ`,
this bundle states that the chart pullback
`chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm`
has a **planar `KthRootSubstitution`** of order `k` at the chart image
`(chartAt ℂ x₀) x₀`, computing the chart-image of the basepoint value
`chartN (f̃ x₀)`.

The bundle additionally records that `f̃ x₀ ≠ ∞`, so `chartN` is the
correct codomain chart at `f̃ x₀` (we are at a finite value of `f̃`).

This is exactly the data required to apply the planar machinery of
ZZ74/ZZ75 to the chart pullback. -/
structure LocalMultiplicityOnManifoldHypothesis
    (f̃ : X → RiemannSphere) (x₀ : X) (k : ℕ) : Prop where
  /-- The basepoint is a finite value of `f̃` (so `chartN` is the right
  codomain chart). -/
  finite_value : f̃ x₀ ≠ (∞ : RiemannSphere)
  /-- The chart-pullback representative satisfies the planar
  `KthRootSubstitution` bundle of order `k` (ZZ75). -/
  planar_substitution :
    KthRootSubstitution
      (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀)
      (RiemannSphere.chartN (f̃ x₀))
      k

/-- **Build the `k = 1` manifold bundle from planar chart-pullback data.**

If the chart pullback `chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm` is analytic on
`closedBall ((chartAt ℂ x₀) x₀) R` with non-vanishing derivative at the
chart image, and `f̃ x₀ ≠ ∞`, then the manifold-level
`LocalMultiplicityOnManifoldHypothesis f̃ x₀ 1` holds. -/
theorem localMultiplicityOnManifoldHypothesis_one_of_chartPullbackAnalytic
    {f̃ : X → RiemannSphere} {x₀ : X} {R : ℝ} (hR : 0 < R)
    (h_finite : f̃ x₀ ≠ (∞ : RiemannSphere))
    (h_an : AnalyticOnNhd ℂ
      (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
      (Metric.closedBall ((chartAt ℂ x₀) x₀) R))
    (hd : deriv (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
          ((chartAt ℂ x₀) x₀) ≠ 0) :
    LocalMultiplicityOnManifoldHypothesis f̃ x₀ 1 := by
  have h_base : (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) = RiemannSphere.chartN (f̃ x₀) := by
    have hx₀_src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
    show RiemannSphere.chartN
        (f̃ ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀))) =
      RiemannSphere.chartN (f̃ x₀)
    rw [(chartAt ℂ x₀).left_inv hx₀_src]
  refine ⟨h_finite, ?_⟩
  exact kthRootSubstitution_of_localMultiplicityOne
          (g := RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
          (x₀ := (chartAt ℂ x₀) x₀)
          (w₀ := RiemannSphere.chartN (f̃ x₀))
          hR h_an h_base hd

/-- **`k = 1` chart-pullback preimage count on the manifold.**

Given the tier-2 bundle `LocalMultiplicityOnManifoldHypothesis f̃ x₀ 1`,
there exist `ε > 0` and `δ > 0` such that for every chart-image value
`w ∈ Metric.ball (chartN (f̃ x₀)) δ` with `w ≠ chartN (f̃ x₀)`, the
**chart-pullback** preimage set has cardinality `1`:
`{z ∈ ball ((chartAt ℂ x₀) x₀) ε | (chartN ∘ f̃ ∘ c.symm) z = w}.ncard = 1`.

This is the chart-pullback formulation; the genuine manifold-level
count `{x | f̃ x = y}.ncard = 1` follows by chart bijectivity once a
stays-finite hypothesis on `f̃` near `x₀` is supplied — see the file
header. -/
theorem localMultiplicityOnManifold_preimage_card_one
    {f̃ : X → RiemannSphere} {x₀ : X}
    (h : LocalMultiplicityOnManifoldHypothesis f̃ x₀ 1) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (RiemannSphere.chartN (f̃ x₀)) δ,
        w ≠ RiemannSphere.chartN (f̃ x₀) →
        ({z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ε |
            (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm) z = w}
          : Set ℂ).ncard = 1 := by
  obtain ⟨_h_finite, hsub⟩ := h
  have h_base : (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) = RiemannSphere.chartN (f̃ x₀) := by
    have hx₀_src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
    show RiemannSphere.chartN
        (f̃ ((chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀))) =
      RiemannSphere.chartN (f̃ x₀)
    rw [(chartAt ℂ x₀).left_inv hx₀_src]
  have h_planar :=
    localKFoldMultiplicity_preimage_card_of_substitution_one hsub h_base
  obtain ⟨ε, hε_pos, δ, hδ_pos, h_count⟩ := h_planar
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw_ball' : w ∈ Metric.ball
      ((RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
        ((chartAt ℂ x₀) x₀)) δ := by
    rw [h_base]; exact hw_ball
  have hw_ne' : w ≠ (RiemannSphere.chartN ∘ f̃ ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) := by
    rw [h_base]; exact hw_ne
  exact h_count w hw_ball' hw_ne'

end Manifold
end JacobianChallenge

end
