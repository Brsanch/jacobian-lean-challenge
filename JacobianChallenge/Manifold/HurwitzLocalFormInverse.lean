/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalForm
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Local analytic inverse for the Hurwitz biholomorphism `ψ`

`hurwitz_local_form` produces an analytic `ψ` at `x₀` with
`ψ x₀ = 0`, `deriv ψ x₀ ≠ 0`, `g z - w₀ = ψ z ^ k` on a disc. By the
inverse function theorem for analytic functions (mathlib
`AnalyticAt.analyticAt_localInverse`), `ψ` has an analytic local
inverse `φ` at `0 = ψ x₀` with

* `φ 0 = x₀`,
* `ψ (φ s) = s` eventually in `s` near `0`,
* `φ (ψ z) = z` eventually in `z` near `x₀`.

This sets up the **target coordinate** `s = ψ(z)` in which the source-
side local k-fold cover takes the clean form `s ↦ s^k`. Downstream
chips will combine `φ` with the cyclic-sum descent to identify the
chart-coefficient of `f_*α` near a critical value with `Q(s^k) / k`.

No `sorry`, no `axiom`. -/

open Filter Topology Metric

namespace JacobianChallenge
namespace Manifold

/-- **Hurwitz local form with analytic local inverse.**

Strengthens `hurwitz_local_form` with the existence of an analytic
local inverse `φ` of the Hurwitz biholomorphism `ψ` at `0`.

Outputs:
* `R > 0`, `ψ : ℂ → ℂ` analytic on `closedBall x₀ R`,
* `ψ x₀ = 0`, `deriv ψ x₀ ≠ 0`,
* `g z - w₀ = ψ z ^ k` on `closedBall x₀ R`,
* `φ : ℂ → ℂ` analytic at `0`,
* `φ 0 = x₀`,
* `ψ (φ s) = s` eventually in `s` near `0`,
* `φ (ψ z) = z` eventually in `z` near `x₀`. -/
theorem hurwitz_local_form_with_inverse
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ (R : ℝ) (ψ : ℂ → ℂ) (φ : ℂ → ℂ),
      0 < R ∧
      AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R) ∧
      ψ x₀ = 0 ∧ deriv ψ x₀ ≠ 0 ∧
      (∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k) ∧
      AnalyticAt ℂ φ 0 ∧
      φ 0 = x₀ ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s) ∧
      (∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) := by
  -- Step 1. Get the Hurwitz local form.
  obtain ⟨R, hR_pos, ψ, hψ_an, hψ_x₀, hψ'_ne, h_fact⟩ :=
    hurwitz_local_form hk hg h_w₀ hord
  have hψ_at_x₀ : AnalyticAt ℂ ψ x₀ :=
    hψ_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  -- Step 2. Apply the analytic inverse function theorem.
  let φ : ℂ → ℂ := hψ_at_x₀.hasStrictDerivAt.localInverse ψ (deriv ψ x₀) x₀ hψ'_ne
  have hφ_an_at_ψ_x₀ : AnalyticAt ℂ φ (ψ x₀) :=
    hψ_at_x₀.analyticAt_localInverse hψ'_ne
  -- Rewrite the analyticity hypothesis to `AnalyticAt ℂ φ 0` using `ψ x₀ = 0`.
  have hφ_an : AnalyticAt ℂ φ 0 := by rw [← hψ_x₀]; exact hφ_an_at_ψ_x₀
  -- `φ (ψ x₀) = x₀` from the inverse-function library.
  have hφ_ψ_x₀ : φ (ψ x₀) = x₀ :=
    HasStrictFDerivAt.localInverse_apply_image ..
  have hφ_0 : φ 0 = x₀ := by rw [← hψ_x₀]; exact hφ_ψ_x₀
  -- Right inverse: `ψ (φ s) = s` eventually for `s` near `ψ x₀ = 0`.
  have h_right : ∀ᶠ s in 𝓝 (ψ x₀), ψ (φ s) = s :=
    HasStrictDerivAt.eventually_right_inverse hψ_at_x₀.hasStrictDerivAt hψ'_ne
  have h_right_at_0 : ∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s := by
    rw [← hψ_x₀]; exact h_right
  -- Left inverse: `φ (ψ z) = z` eventually for `z` near `x₀`.
  have h_left : ∀ᶠ z in 𝓝 x₀, φ (ψ z) = z :=
    HasStrictDerivAt.eventually_left_inverse hψ_at_x₀.hasStrictDerivAt hψ'_ne
  -- Package.
  exact ⟨R, ψ, φ, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
         h_right_at_0, h_left⟩

end Manifold
end JacobianChallenge
