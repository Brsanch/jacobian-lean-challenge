/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalForm
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Derivative formula for the Hurwitz local form

For `g - w₀ = ψ^k` on `closedBall x₀ R`, differentiating both sides:

  `deriv g w = k · ψ(w)^(k-1) · deriv ψ w`   for `w ∈ Metric.ball x₀ R`.

The proof composes:
* `HasDerivAt ψ (deriv ψ w) w` (analytic ⟹ differentiable)
* `HasDerivAt.pow` for `ψ^k`
* `HasDerivAt.const_add` for `w₀ + ψ^k`
* The pointwise identity `g w = w₀ + ψ(w)^k` (from `h_fact`) to transport
  the derivative.

Consequence: for `w` near `x₀` with `ψ(w) ≠ 0` and `deriv ψ w ≠ 0`,
`deriv g w ≠ 0` (so `w` is a regular point of the chart-pullback).

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Derivative formula** for the Hurwitz local form.

For `g, ψ : ℂ → ℂ` with `g - w₀ = ψ^k` on `closedBall x₀ R`, and ψ
analytic on the closed ball, the derivative of g at any open-ball point
factors:

  `deriv g w = ↑k · ψ(w)^(k-1) · deriv ψ w`. -/
theorem hurwitz_deriv_formula
    {g ψ : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R : ℝ}
    (_hR_pos : 0 < R)
    (hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R))
    (h_fact : ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k)
    {w : ℂ} (hw : w ∈ Metric.ball x₀ R) :
    HasDerivAt g ((k : ℂ) * (ψ w) ^ (k - 1) * deriv ψ w) w := by
  -- ψ analytic on the open ball.
  have hψ_at_w : AnalyticAt ℂ ψ w := hψ_an w (Metric.ball_subset_closedBall hw)
  have hψ_diff : DifferentiableAt ℂ ψ w := hψ_at_w.differentiableAt
  have hψ_hasDeriv : HasDerivAt ψ (deriv ψ w) w := hψ_diff.hasDerivAt
  -- ψ^k has derivative k · ψ(w)^(k-1) · deriv ψ w.
  have h_pow_hasDeriv :
      HasDerivAt (fun y => (ψ y) ^ k)
        ((k : ℂ) * (ψ w) ^ (k - 1) * deriv ψ w) w :=
    hψ_hasDeriv.pow k
  -- `w₀ + ψ^k` has the same derivative.
  have h_aux_hasDeriv :
      HasDerivAt (fun y => w₀ + (ψ y) ^ k)
        ((k : ℂ) * (ψ w) ^ (k - 1) * deriv ψ w) w :=
    h_pow_hasDeriv.const_add w₀
  -- `g y = w₀ + ψ(y)^k` on `closedBall x₀ R`, which is a nbhd of w (in `ball x₀ R`).
  have h_ball_nhds : Metric.ball x₀ R ∈ 𝓝 w :=
    Metric.isOpen_ball.mem_nhds hw
  have h_g_eq : g =ᶠ[𝓝 w] (fun y => w₀ + (ψ y) ^ k) := by
    filter_upwards [h_ball_nhds] with y hy
    have hy_closed : y ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hy
    have := h_fact y hy_closed
    linear_combination this
  -- Transfer the derivative via congruence.
  exact h_aux_hasDeriv.congr_of_eventuallyEq h_g_eq

/-- **Non-vanishing of the Hurwitz derivative away from x₀.**

For `w ∈ Metric.ball x₀ R` with `ψ(w) ≠ 0` and `deriv ψ w ≠ 0`, and
`k ≥ 1`, the derivative of g at w is non-zero. -/
theorem hurwitz_deriv_ne_zero
    {g ψ : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R : ℝ}
    (hR_pos : 0 < R)
    (hψ_an : AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R))
    (h_fact : ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k)
    (hk : 1 ≤ k)
    {w : ℂ} (hw : w ∈ Metric.ball x₀ R)
    (hψw_ne : ψ w ≠ 0) (hψ'w_ne : deriv ψ w ≠ 0) :
    deriv g w ≠ 0 := by
  have h_deriv := hurwitz_deriv_formula hR_pos hψ_an h_fact hw
  rw [h_deriv.deriv]
  -- k · ψ(w)^(k-1) · deriv ψ w ≠ 0
  have hk_ne_ℂ : (k : ℂ) ≠ 0 := by
    have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    exact_mod_cast hk_ne
  have hψ_pow_ne : (ψ w) ^ (k - 1) ≠ 0 := pow_ne_zero _ hψw_ne
  exact mul_ne_zero (mul_ne_zero hk_ne_ℂ hψ_pow_ne) hψ'w_ne

end Manifold
end JacobianChallenge
