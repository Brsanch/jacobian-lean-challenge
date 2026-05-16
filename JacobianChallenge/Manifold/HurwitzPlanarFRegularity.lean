/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzDerivFormula
import JacobianChallenge.Manifold.HurwitzDerivPsiNonzero
import JacobianChallenge.Manifold.HurwitzZetaLocalNonzero

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Planar f-regularity at Hurwitz fibre points

Combines:
* chip 3d-12 (Hurwitz derivative formula `deriv g = k · ψ^(k-1) · ψ'`)
* chip 3d-13 (`deriv ψ z ≠ 0` eventually)
* chip 3c-6 (`ψ z ≠ 0` for z ≠ x₀)

to conclude: for z near x₀ with z ≠ x₀, in the open Hurwitz disc,
`deriv g z ≠ 0`. This is the **planar regularity** condition on
the chart-pullback g at Hurwitz fibre points; downstream chips lift it
through the manifold/chart structure to f-regularity in the manifold.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Planar f-regularity at Hurwitz fibre points.**

For Hurwitz `g - w₀ = ψ^k` on `closedBall x₀ R` with `ψ x₀ = 0`,
`deriv ψ x₀ ≠ 0`, and an eventual left-inverse `φ` with
`φ ∘ ψ = id`:

  ∀ᶠ z in 𝓝 x₀, z ≠ x₀ → z ∈ Metric.ball x₀ R → deriv g z ≠ 0. -/
theorem hurwitz_planar_f_regular
    {g ψ φ : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R : ℝ}
    (hR_pos : 0 < R)
    (hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R))
    (hψ_x₀ : ψ x₀ = 0) (hψ'_ne : deriv ψ x₀ ≠ 0)
    (h_fact : ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k)
    (h_left : ∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) (hk : 1 ≤ k) :
    ∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
      z ∈ Metric.ball x₀ R → deriv g z ≠ 0 := by
  have h_ψ_ne : ∀ᶠ z in 𝓝 x₀, z ≠ x₀ → ψ z ≠ 0 :=
    hurwitz_ne_zero_of_ne_x₀ hψ_x₀ h_left
  have h_derivψ_ne : ∀ᶠ z in 𝓝 x₀, deriv ψ z ≠ 0 :=
    hurwitz_deriv_psi_eventually_ne_zero hR_pos hψ_an hψ'_ne
  filter_upwards [h_ψ_ne, h_derivψ_ne] with z h_ψ_imp h_derivψ_ne_z hne hball
  exact hurwitz_deriv_ne_zero hR_pos hψ_an h_fact hk hball
    (h_ψ_imp hne) h_derivψ_ne_z

end Manifold
end JacobianChallenge
