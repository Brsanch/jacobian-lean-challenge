/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCyclicSumDescentZForm
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level Hurwitz + cyclic-sum descent at a critical fibre point

Specialises the pure-analytic `hurwitz_cyclic_sum_descent_zForm`
(chip 3c-5) to the manifold setting:

* `g := f.chartPullback z₀` — the chart pullback of `f` at `z₀`.
* `h := α.localCoeff z₀` — the chart-`z₀` local coefficient of `α`.
* `x₀ := (chartAt ℂ z₀) z₀` — the chart image of `z₀`.
* `w₀ := (chartAt ℂ (f.toRiemannSphere z₀)) (f.toRiemannSphere z₀)` —
  the chart image of `f.toRiemannSphere z₀`.

Both `g` and `h` are analytic at `x₀` (via `analyticAt_chartPullback`
and `localCoeff_analyticAt_chart_image`). The hypothesis
`analyticOrderAt (g - w₀) x₀ = ↑k` with `k ≥ 2` is supplied by the
caller (the critical fibre point z₀ has ramification index `k`).

Output: `ψ, φ, Q` analytic data plus the source-side z-form

  `∀ᶠ z in 𝓝 z₀, cyclicSum (α.localCoeff z₀ ∘ φ) ζ k (ψ ((chartAt ℂ z₀) z)) =`
  `   (ψ ((chartAt ℂ z₀) z))^(k-1) · Q (f.chartPullback z₀ ((chartAt ℂ z₀) z) - w₀)`

(eventually in `z ∈ X` near `z₀`, via `Tendsto.eventually` on
`z ↦ (chartAt ℂ z₀) z`).

This is the bundle-wiring entry-point for the trace-extension chip arc.

No `sorry`, no `axiom`. -/

open Filter Topology Set
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold-level Hurwitz + cyclic-sum descent at a fibre point.**

For `f : MeromorphicNonzero X` and `z₀ : X` with chart pullback of
order `k ≥ 2` at `z₀` (i.e. `analyticOrderAt (g - w₀) x₀ = ↑k`,
`g := f.chartPullback z₀`, `x₀ := (chartAt ℂ z₀) z₀`, `w₀ := g x₀`),
and `α : HolomorphicOneForm X`, primitive `k`-th root `ζ`,
the cyclic-sum descent produces `ψ, φ, Q` analytic with the eventual
source-side identity in `x : ℂ` near `x₀`. -/
theorem chartPullback_cyclic_sum_descent
    [DecidableEq X]
    (f : MeromorphicNonzero X) (z₀ : X)
    (α : HolomorphicOneForm X)
    {ζ : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hζ : IsPrimitiveRoot ζ k)
    (hord : analyticOrderAt
      (fun z => f.chartPullback z₀ z
        - f.chartPullback z₀ ((chartAt ℂ z₀) z₀))
      ((chartAt ℂ z₀) z₀) = (k : ℕ∞)) :
    ∃ (R : ℝ) (ψ : ℂ → ℂ) (φ : ℂ → ℂ) (Q : ℂ → ℂ),
      0 < R ∧
      AnalyticOnNhd ℂ ψ (Metric.closedBall ((chartAt ℂ z₀) z₀) R) ∧
      ψ ((chartAt ℂ z₀) z₀) = 0 ∧ deriv ψ ((chartAt ℂ z₀) z₀) ≠ 0 ∧
      (∀ x ∈ Metric.closedBall ((chartAt ℂ z₀) z₀) R,
        f.chartPullback z₀ x - f.chartPullback z₀ ((chartAt ℂ z₀) z₀)
          = (ψ x) ^ k) ∧
      AnalyticAt ℂ φ 0 ∧
      φ 0 = (chartAt ℂ z₀) z₀ ∧
      AnalyticAt ℂ Q 0 ∧
      (∀ᶠ x in 𝓝 ((chartAt ℂ z₀) z₀),
        JacobianChallenge.cyclicSum (α.localCoeff z₀ ∘ φ) ζ k (ψ x)
          = (ψ x) ^ (k - 1)
            * Q (f.chartPullback z₀ x - f.chartPullback z₀ ((chartAt ℂ z₀) z₀))) := by
  -- Analyticity of `g := f.chartPullback z₀` at `x₀ := (chartAt ℂ z₀) z₀`.
  have hg : AnalyticAt ℂ (f.chartPullback z₀) ((chartAt ℂ z₀) z₀) :=
    f.analyticAt_chartPullback z₀
  -- Analyticity of `h := α.localCoeff z₀` at `x₀`.
  have h_an : AnalyticAt ℂ (α.localCoeff z₀) ((chartAt ℂ z₀) z₀) :=
    α.localCoeff_analyticAt_chart_image z₀
  -- Apply the pure-analytic z-form descent.
  exact Manifold.hurwitz_cyclic_sum_descent_zForm
    (g := f.chartPullback z₀)
    (h := α.localCoeff z₀)
    (x₀ := (chartAt ℂ z₀) z₀)
    (w₀ := f.chartPullback z₀ ((chartAt ℂ z₀) z₀))
    (k := k) hk hg rfl hord h_an hζ

end MeromorphicNonzero
end JacobianChallenge

end
