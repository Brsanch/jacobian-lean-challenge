/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzPlanarFRegularity
import JacobianChallenge.Manifold.HurwitzLocalFormInverse

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Eventual planar f-regularity at Hurwitz fibre points

For ξ ≠ 0 near `0` and `j ∈ range k`, the Hurwitz fibre point
`φ(ζ^j · ξ)` is regular: `deriv g (φ(ζ^j · ξ)) ≠ 0`.

Composition of:
* chip 3d-14 (planar f-regularity for `z` near `x₀` with `z ≠ x₀`,
  `z ∈ Metric.ball x₀ R`)
* `Tendsto` on `ξ ↦ φ(ζ^j · ξ)` (continuous at 0, image is `x₀`)
* ψ-injectivity (from chip 3c-6 reasoning): `φ(ζ^j · ξ) ≠ x₀` for
  `ζ^j · ξ ≠ 0`, hence for `ξ ≠ 0` (and `ζ ≠ 0`).
* `φ(ζ^j · ξ) ∈ Metric.ball x₀ R` for `ξ` small enough (continuity of
  φ + Hurwitz radius).

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Eventual planar f-regularity at Hurwitz fibre points.**

For ξ ≠ 0 sufficiently small, the chart-pullback derivative at the
Hurwitz fibre point `φ(ζ^j · ξ)` is non-zero. -/
theorem hurwitz_fibre_regular_planar
    {g ψ φ : ℂ → ℂ} {x₀ w₀ ζ : ℂ} {k j : ℕ} {R : ℝ}
    (hR_pos : 0 < R)
    (hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R))
    (hψ_x₀ : ψ x₀ = 0) (hψ'_ne : deriv ψ x₀ ≠ 0)
    (h_fact : ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k)
    (h_right : ∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s)
    (h_left : ∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) (hk : 1 ≤ k)
    (hζ_ne : ζ ≠ 0)
    (hφ_an : AnalyticAt ℂ φ 0) (hφ_0 : φ 0 = x₀) :
    ∀ᶠ ξ in 𝓝 (0 : ℂ),
      ξ ≠ 0 → deriv g (φ (ζ ^ j * ξ)) ≠ 0 := by
  -- 1. Tendsto: `φ(ζ^j · ξ) →[ξ→0] x₀`.
  have hφ_cont : ContinuousAt φ 0 := hφ_an.continuousAt
  have hφ_tendsto : Tendsto (fun ξ : ℂ => φ (ζ ^ j * ξ)) (𝓝 0) (𝓝 x₀) := by
    have h_mul : Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 0) (𝓝 (ζ ^ j * 0)) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto
      simpa using this
    have h_step : Tendsto (fun ξ : ℂ => φ (ζ ^ j * ξ)) (𝓝 0) (𝓝 (φ 0)) :=
      hφ_cont.tendsto.comp h_mul
    simpa [hφ_0] using h_step
  -- 2. Planar f-regularity (chip 3d-14): pulled back to `ξ`.
  have h_planar : ∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
      z ∈ Metric.ball x₀ R → deriv g z ≠ 0 :=
    hurwitz_planar_f_regular hR_pos hψ_an hψ_x₀ hψ'_ne h_fact h_left hk
  have h_planar_pulled : ∀ᶠ ξ in 𝓝 (0 : ℂ),
      φ (ζ ^ j * ξ) ≠ x₀ →
      φ (ζ ^ j * ξ) ∈ Metric.ball x₀ R →
      deriv g (φ (ζ ^ j * ξ)) ≠ 0 :=
    hφ_tendsto.eventually h_planar
  -- 3. `φ(ζ^j · ξ) ∈ Metric.ball x₀ R` for ξ small (open ball is open ⟹ nbhd of x₀).
  have h_ball_nhds : Metric.ball x₀ R ∈ 𝓝 x₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR_pos)
  have h_ball_pulled : ∀ᶠ ξ in 𝓝 (0 : ℂ),
      φ (ζ ^ j * ξ) ∈ Metric.ball x₀ R :=
    hφ_tendsto.eventually_mem h_ball_nhds
  -- 4. `φ(ζ^j · ξ) ≠ x₀` for `ξ ≠ 0`: from h_right at `ζ^j · ξ`,
  -- `ψ (φ(ζ^j · ξ)) = ζ^j · ξ`. If `φ(ζ^j · ξ) = x₀`, then `ψ x₀ = ζ^j · ξ`,
  -- but `ψ x₀ = 0`, so `ζ^j · ξ = 0`, hence `ξ = 0` (since `ζ^j ≠ 0`).
  have h_mul_tendsto : Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 0) (𝓝 (ζ ^ j * 0)) :=
      (continuous_const.mul continuous_id).continuousAt.tendsto
    simpa using this
  have h_right_pulled : ∀ᶠ ξ in 𝓝 (0 : ℂ), ψ (φ (ζ ^ j * ξ)) = ζ ^ j * ξ :=
    h_mul_tendsto.eventually h_right
  filter_upwards [h_planar_pulled, h_ball_pulled, h_right_pulled] with
    ξ h_imp h_ball h_psi hξ_ne
  -- Prove `φ(ζ^j · ξ) ≠ x₀`.
  have h_ne_x₀ : φ (ζ ^ j * ξ) ≠ x₀ := by
    intro h_eq
    rw [h_eq, hψ_x₀] at h_psi
    have hζj_ne : ζ ^ j ≠ 0 := pow_ne_zero _ hζ_ne
    have h_zero : ζ ^ j * ξ = 0 := h_psi.symm
    exact hξ_ne ((mul_eq_zero.mp h_zero).resolve_left hζj_ne)
  exact h_imp h_ne_x₀ h_ball

end Manifold
end JacobianChallenge
