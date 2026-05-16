/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCyclicSumDescentOneFormDivided
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level 1-form-corrected divided form at a fibre point

Specialises the pure-analytic `hurwitz_cyclic_sum_descent_oneForm_divided`
(chip 3d-3) to the manifold setting: applies it with
`g := f.chartPullback z₀` and `h := α.localCoeff z₀`, both analytic at
`x₀ := (chartAt ℂ z₀) z₀`.

Output: ψ, φ, Q with the **chart-coefficient identification** at
regular values near the critical value `w₀ := f.chartPullback z₀ x₀`:

  ∀ᶠ x in 𝓝 x₀, x ≠ x₀ →
    cyclicSum ((α.localCoeff z₀ / deriv ψ) ∘ φ) ζ k (ψ x)
        / ((↑k) · (ψ x)^(k-1))
      = Q (f.chartPullback z₀ x - w₀) / ↑k.

LHS = chart-coefficient of the trace 1-form `f_*α` at the regular value
(via the local k-fold cover + cotangent pullback formula, supplied
downstream). RHS = `Q / k`, the analytic extension across the critical
value `w₀`.

This is the bundle-wiring **chart-coefficient identification** chip —
the final pure-analytic-plus-chart-pullback ingredient before the
sheet/cotangent-pullback identification on the source side.

No `sorry`, no `axiom`. -/

open Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold-level 1-form-corrected divided descent at a fibre point.**

For `f : MeromorphicNonzero X`, `z₀ : X` with chart-pullback of order
`k ≥ 2` at `(chartAt ℂ z₀) z₀`, primitive k-th root `ζ`, and
`α : HolomorphicOneForm X`, the descent produces ψ, φ, Q with the
chart-coefficient identification at regular values near the critical
value. -/
theorem chartPullback_cyclic_sum_descent_oneForm_divided
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
      (∀ᶠ x in 𝓝 ((chartAt ℂ z₀) z₀), x ≠ (chartAt ℂ z₀) z₀ →
        JacobianChallenge.cyclicSum
            ((fun z => α.localCoeff z₀ z / deriv ψ z) ∘ φ) ζ k (ψ x)
              / ((k : ℂ) * (ψ x) ^ (k - 1))
          = Q (f.chartPullback z₀ x
              - f.chartPullback z₀ ((chartAt ℂ z₀) z₀)) / (k : ℂ)) := by
  have hg : AnalyticAt ℂ (f.chartPullback z₀) ((chartAt ℂ z₀) z₀) :=
    f.analyticAt_chartPullback z₀
  have h_an : AnalyticAt ℂ (α.localCoeff z₀) ((chartAt ℂ z₀) z₀) :=
    α.localCoeff_analyticAt_chart_image z₀
  exact Manifold.hurwitz_cyclic_sum_descent_oneForm_divided
    (g := f.chartPullback z₀)
    (h := α.localCoeff z₀)
    (x₀ := (chartAt ℂ z₀) z₀)
    (w₀ := f.chartPullback z₀ ((chartAt ℂ z₀) z₀))
    (k := k) hk hg rfl hord h_an hζ

end MeromorphicNonzero
end JacobianChallenge

end
