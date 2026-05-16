/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalFormInverse
import JacobianChallenge.Manifold.CyclicSumFactorKthPowerDescent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Hurwitz form + cyclic-sum descent composition

Given an analytic `g : ℂ → ℂ` at `x₀` with `analyticOrderAt (g - w₀) x₀ = k`
(`k ≥ 2`), Hurwitz local form supplies `ψ` with `g z - w₀ = ψ z ^ k` and
its analytic local inverse `φ` at `0 = ψ x₀`.

For any analytic `h : ℂ → ℂ` at `x₀` and primitive `k`-th root `ω`, the
cyclic-sum-factor descent applied to the **transported** coefficient
`h ∘ φ` (which is analytic at `0`, since `φ 0 = x₀`) produces `Q`
analytic at `0` with

  `cyclicSum (h ∘ φ) ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)`   (eventually).

This is the structural composition that downstream chips will lift to
the manifold/cotangent-bundle level: `h ∘ φ` is the source-side chart
coefficient of α expressed in the Hurwitz coordinate `s = ψ(z)`, and
`Q` is the chart coefficient of `f_*α` in the target coordinate
`v = s ^ k = g(z) - w₀`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Hurwitz form + cyclic-sum-factor descent.**

For analytic `g, h : ℂ → ℂ` at `x₀` with `g x₀ = w₀` and analytic order
of `g - w₀` at `x₀` equal to `k` (`k ≥ 2`), and a primitive `k`-th root
of unity `ω`, there exist:

* a Hurwitz biholomorphism `ψ` on a disc `closedBall x₀ R` with
  `ψ x₀ = 0`, `deriv ψ x₀ ≠ 0`, and `g z - w₀ = ψ z ^ k`,
* an analytic local inverse `φ` at `0` with `φ 0 = x₀`,
* a function `Q` analytic at `0`,

such that the cyclic-sum identity holds eventually:

  `cyclicSum (h ∘ φ) ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)`. -/
theorem hurwitz_cyclic_sum_descent
    {g h : ℂ → ℂ} {x₀ w₀ ω : ℂ} {k : ℕ}
    (hk : 2 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞))
    (h_an : AnalyticAt ℂ h x₀)
    (hω : IsPrimitiveRoot ω k) :
    ∃ (R : ℝ) (ψ : ℂ → ℂ) (φ : ℂ → ℂ) (Q : ℂ → ℂ),
      0 < R ∧
      AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R) ∧
      ψ x₀ = 0 ∧ deriv ψ x₀ ≠ 0 ∧
      (∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k) ∧
      AnalyticAt ℂ φ 0 ∧
      φ 0 = x₀ ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s) ∧
      (∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) ∧
      AnalyticAt ℂ Q 0 ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ),
        JacobianChallenge.cyclicSum (h ∘ φ) ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)) := by
  have hk_pos : 1 ≤ k := by omega
  -- Step 1. Hurwitz with inverse.
  obtain ⟨R, ψ, φ, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          h_right, h_left⟩ :=
    hurwitz_local_form_with_inverse hk_pos hg h_w₀ hord
  -- Step 2. `h ∘ φ` is analytic at `0` (via `φ 0 = x₀`).
  have h_comp_an : AnalyticAt ℂ (h ∘ φ) 0 := by
    have hh_at : AnalyticAt ℂ h (φ 0) := by rw [hφ_0]; exact h_an
    exact hh_at.comp hφ_an
  -- Step 3. Apply cyclic-sum-factor descent to `h ∘ φ`.
  obtain ⟨Q, Q_an, hQ_eq⟩ :=
    JacobianChallenge.cyclicSum_factor_descends_to_kth_power
      (h := h ∘ φ) hω hk h_comp_an
  -- Package.
  exact ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
         h_right, h_left, Q_an, hQ_eq⟩

end Manifold
end JacobianChallenge
