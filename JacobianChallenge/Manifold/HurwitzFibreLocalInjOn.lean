/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzFibreRegularPlanar
import JacobianChallenge.Manifold.LocalBiholomorphism

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Planar local injectivity at Hurwitz fibre points

For ξ ≠ 0 sufficiently small, the chart-pullback `g` is locally
injective at `φ(ζ^j · ξ)`: there exists `U ∈ 𝓝 (φ(ζ^j · ξ))` with
`Set.InjOn g U`.

Combines chip 3d-15 (`deriv g (φ(ζ^j · ξ)) ≠ 0`) and
`AnalyticAt.exists_local_biholomorphism` (planar inverse function
theorem packaged in `LocalBiholomorphism.lean`).

**Caller-supplied analyticity hypothesis.** We require
`AnalyticAt ℂ g (φ(ζ^j · ξ))` for each ξ — since `g := f.chartPullback z₀`
is analytic on the entire chart target (via ω-smoothness + chart
transitions), this is supplied downstream from a chart-domain
analyticity chip. We expose `g_an_at` as an explicit hypothesis.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Planar local injectivity at Hurwitz fibre points.**

For ξ ≠ 0 sufficiently small with `g` analytic at `φ(ζ^j · ξ)`, there
exists an open neighbourhood `U ∋ φ(ζ^j · ξ)` on which `g` is injective. -/
theorem hurwitz_fibre_local_injOn_planar
    {g ψ φ : ℂ → ℂ} {x₀ w₀ ζ : ℂ} {k j : ℕ} {R : ℝ}
    (hR_pos : 0 < R)
    (hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R))
    (hψ_x₀ : ψ x₀ = 0) (hψ'_ne : deriv ψ x₀ ≠ 0)
    (h_fact : ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k)
    (h_right : ∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s)
    (h_left : ∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) (hk : 1 ≤ k)
    (hζ_ne : ζ ≠ 0)
    (hφ_an : AnalyticAt ℂ φ 0) (hφ_0 : φ 0 = x₀)
    (g_an_at : ∀ᶠ ξ in 𝓝 (0 : ℂ), AnalyticAt ℂ g (φ (ζ ^ j * ξ))) :
    ∀ᶠ ξ in 𝓝 (0 : ℂ),
      ξ ≠ 0 → ∃ U : Set ℂ, U ∈ 𝓝 (φ (ζ ^ j * ξ)) ∧ Set.InjOn g U := by
  have h_deriv :=
    hurwitz_fibre_regular_planar hR_pos hψ_an hψ_x₀ hψ'_ne h_fact
      h_right h_left hk hζ_ne hφ_an hφ_0 (j := j)
  filter_upwards [h_deriv, g_an_at] with ξ h_deriv_imp h_g_an hξ_ne
  -- Apply planar IFT.
  obtain ⟨U, hU_nhds, V, _hV_nhds, φ_inv, _hMapsTo_uv, _hMapsTo_vu, hLeftInv, _hRightInv,
          _hφ_inv_an⟩ :=
    AnalyticAt.exists_local_biholomorphism h_g_an (h_deriv_imp hξ_ne)
  -- `LeftInvOn φ_inv g U` implies `InjOn g U`.
  exact ⟨U, hU_nhds, hLeftInv.injOn⟩

end Manifold
end JacobianChallenge
