/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalForm
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `deriv ψ z ≠ 0` for z near x₀

For Hurwitz ψ with `ψ x₀ = 0`, `deriv ψ x₀ ≠ 0`, and ψ analytic on a
closed disc around x₀: `deriv ψ` is continuous at x₀ (analytic ⟹
continuous derivative), so by `ContinuousAt.eventually_ne`,
`deriv ψ z ≠ 0` for z in a neighbourhood of x₀.

Used downstream with `hurwitz_deriv_ne_zero` (chip 3d-12) to get
f-regularity at Hurwitz fibre points.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Eventual non-vanishing of deriv ψ near x₀.**

For ψ analytic on `closedBall x₀ R` with `deriv ψ x₀ ≠ 0`,
`deriv ψ z ≠ 0` for z in a neighbourhood of x₀. -/
theorem hurwitz_deriv_psi_eventually_ne_zero
    {ψ : ℂ → ℂ} {x₀ : ℂ} {R : ℝ}
    (hR_pos : 0 < R)
    (hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R))
    (hψ'_ne : deriv ψ x₀ ≠ 0) :
    ∀ᶠ z in 𝓝 x₀, deriv ψ z ≠ 0 := by
  -- ψ analytic at x₀ ⟹ deriv ψ analytic at x₀ ⟹ continuous at x₀.
  have hψ_at_x₀ : AnalyticAt ℂ ψ x₀ :=
    hψ_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  have h_deriv_an : AnalyticAt ℂ (deriv ψ) x₀ := hψ_at_x₀.deriv
  have h_deriv_cont : ContinuousAt (deriv ψ) x₀ := h_deriv_an.continuousAt
  -- `ContinuousAt.eventually_ne`.
  exact h_deriv_cont.eventually_ne hψ'_ne

end Manifold
end JacobianChallenge
