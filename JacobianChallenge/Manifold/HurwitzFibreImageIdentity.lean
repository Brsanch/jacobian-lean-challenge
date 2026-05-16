/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalFormInverse

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pure-planar fibre-image identity: `g (φ (ζ^j · ξ)) - w₀ = ξ^k`

For the Hurwitz local form `g - w₀ = ψ^k` with analytic local inverse
`φ` (chip 3c-2), and `ζ` a `k`-th root of unity (`ζ^k = 1`), the
parameterized point `φ (ζ^j · ξ)` is a preimage of `ξ^k + w₀` under
`g` for ξ near 0:

  `g (φ (ζ^j · ξ)) - w₀ = (ζ^j · ξ)^k = (ζ^k)^j · ξ^k = ξ^k`.

This is the **planar fibre enumeration** identity. Downstream chips lift
this through `(chartAt ℂ z₀).symm` and `(chartAt ℂ v₀).symm` to identify
the manifold-level fibre `f⁻¹(v)` (for `v` regular near critical `v₀`)
with the k points `{(chartAt ℂ z₀).symm (φ (ζ^j ξ)) : j < k}`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Planar fibre-image identity** via Hurwitz parameterization.

Given the Hurwitz form `g - w₀ = ψ^k` on `closedBall x₀ R`, the
analytic local inverse `φ` with `ψ ∘ φ = id` eventually at `0`, and
`ζ` with `ζ^k = 1`, for ξ near 0 with `φ (ζ^j · ξ)` in the Hurwitz disc:

  `g (φ (ζ^j · ξ)) - w₀ = ξ^k`. -/
theorem hurwitz_fibre_image_eq
    {g ψ φ : ℂ → ℂ} {x₀ w₀ ζ : ℂ} {k : ℕ} {R : ℝ}
    (_hR_pos : 0 < R)
    (h_fact : ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k)
    (h_right : ∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s)
    (hζ_pow : ζ ^ k = 1) (j : ℕ) :
    ∀ᶠ ξ in 𝓝 (0 : ℂ), φ (ζ ^ j * ξ) ∈ Metric.closedBall x₀ R →
      g (φ (ζ ^ j * ξ)) - w₀ = ξ ^ k := by
  -- Pull `h_right` back along ξ ↦ ζ^j · ξ.
  have h_mul_tendsto :
      Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have : Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 0) (𝓝 (ζ ^ j * 0)) :=
      (continuous_const.mul continuous_id).continuousAt.tendsto
    simpa using this
  have h_right_pull : ∀ᶠ ξ in 𝓝 (0 : ℂ), ψ (φ (ζ ^ j * ξ)) = ζ ^ j * ξ :=
    h_mul_tendsto.eventually h_right
  filter_upwards [h_right_pull] with ξ hξ_psi hξ_in_disc
  -- `(ψ (φ (ζ^j · ξ)))^k = g (φ (ζ^j · ξ)) - w₀`.
  have h_pow_eq : (ψ (φ (ζ ^ j * ξ))) ^ k = g (φ (ζ ^ j * ξ)) - w₀ :=
    (h_fact (φ (ζ ^ j * ξ)) hξ_in_disc).symm
  -- Substitute `ψ (φ (ζ^j · ξ)) = ζ^j · ξ`.
  rw [hξ_psi] at h_pow_eq
  -- `(ζ^j · ξ)^k = (ζ^k)^j · ξ^k = 1^j · ξ^k = ξ^k`.
  have h_rhs : (ζ ^ j * ξ) ^ k = ξ ^ k := by
    rw [mul_pow, ← pow_mul, mul_comm j k, pow_mul, hζ_pow, one_pow, one_mul]
  rw [h_rhs] at h_pow_eq
  exact h_pow_eq.symm

end Manifold
end JacobianChallenge
