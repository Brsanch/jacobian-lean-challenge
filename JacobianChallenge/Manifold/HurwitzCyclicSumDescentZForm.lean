/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCyclicSumDescentKthRoot

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Source-side z-form of the Hurwitz + cyclic-sum descent

Re-quantifies `hurwitz_cyclic_sum_descent_kthRoot_form` (chip 3c-4)
over `z` near `x₀`, eliminating the explicit k-th root quantifier.

The bridge: for `z` near `x₀`, set `ξ := ψ z`. Then `ξ ^ k = (ψ z)^k =
g z - w₀` by the Hurwitz form. Plugging `ξ := ψ z` and `v := g z - w₀`
into the k-th root form gives the source-side identity:

  `∀ᶠ z in 𝓝 x₀, cyclicSum (h ∘ φ) ω k (ψ z) = (ψ z)^(k-1) * Q (g z - w₀)`.

This is the most directly usable form for the bundle-level chart-
coefficient bridge: the LHS is the cyclic-sum applied to the
transported chart coefficient, evaluated at the Hurwitz coordinate
`ψ z` of a point `z` near a fibre point of the critical value `w₀`;
the RHS is `(ψ z)^(k-1) · Q (target chart coord)`, with `Q` analytic
across the critical value.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Source-side z-form.** Re-quantification of
`hurwitz_cyclic_sum_descent_kthRoot_form` over `z` near `x₀`, using
the Hurwitz identity `(ψ z)^k = g z - w₀`. -/
theorem hurwitz_cyclic_sum_descent_zForm
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
      AnalyticAt ℂ Q 0 ∧
      (∀ᶠ z in 𝓝 x₀,
        JacobianChallenge.cyclicSum (h ∘ φ) ω k (ψ z)
          = (ψ z) ^ (k - 1) * Q (g z - w₀)) := by
  obtain ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          _h_right, _h_left, Q_an, h_v_form⟩ :=
    hurwitz_cyclic_sum_descent_kthRoot_form hk hg h_w₀ hord h_an hω
  refine ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          Q_an, ?_⟩
  -- We need to pull the eventually-in-v back to eventually-in-z.
  -- Strategy: `ψ` is continuous at `x₀` with `ψ x₀ = 0`, so the map
  -- `z ↦ ψ z` tends to `0` at `x₀`. Hence
  -- `∀ᶠ z in 𝓝 x₀, ∀ ξ : ℂ, ξ^k = (ψ z)^k → ...` follows from
  -- `∀ᶠ v in 𝓝 0, ...` via `Tendsto.eventually` applied to v ↦ (ψ z)^k.
  -- We also need `(ψ z)^k = g z - w₀` on a neighbourhood; that's
  -- `h_fact` on the closed ball.
  have hψ_at_x₀ : AnalyticAt ℂ ψ x₀ :=
    hψ_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  have hψ_cont : ContinuousAt ψ x₀ := hψ_at_x₀.continuousAt
  -- `(fun z => ψ z) →[𝓝 x₀] 0` since `ψ x₀ = 0`.
  have hψ_tendsto : Tendsto ψ (𝓝 x₀) (𝓝 0) := by
    have h_to_ψx₀ : Tendsto ψ (𝓝 x₀) (𝓝 (ψ x₀)) := hψ_cont.tendsto
    simpa [hψ_x₀] using h_to_ψx₀
  -- Pull `h_v_form` back: `∀ᶠ z, ∀ ξ, ξ^k = (ψ z)^k → cyclicSum ... = ...`.
  have h_pulled : ∀ᶠ z in 𝓝 x₀, ∀ ξ : ℂ, ξ ^ k = (ψ z) ^ k →
      JacobianChallenge.cyclicSum (h ∘ φ) ω k ξ
        = ξ ^ (k - 1) * Q ((ψ z) ^ k) := by
    -- v ↦ (ψ z)^k composed with z ↦ x₀ tends to 0.
    have h_pow_tendsto : Tendsto (fun z => (ψ z) ^ k) (𝓝 x₀) (𝓝 0) := by
      have : Tendsto (fun z => (ψ z) ^ k) (𝓝 x₀) (𝓝 ((0 : ℂ) ^ k)) :=
        hψ_tendsto.pow k
      have hk_ne : k ≠ 0 := by omega
      simpa [zero_pow hk_ne] using this
    exact h_pow_tendsto.eventually h_v_form
  -- Also need `g z - w₀ = (ψ z)^k` eventually-in-z near x₀ (from `h_fact`).
  have h_eq_event : ∀ᶠ z in 𝓝 x₀, g z - w₀ = (ψ z) ^ k := by
    -- closed ball is a nbhd of x₀ (radius R > 0).
    have hball_nhds : Metric.closedBall x₀ R ∈ 𝓝 x₀ :=
      Metric.closedBall_mem_nhds x₀ hR_pos
    filter_upwards [hball_nhds] with z hz
    exact h_fact z hz
  -- Combine: instantiate `h_pulled` at `ξ := ψ z`.
  filter_upwards [h_pulled, h_eq_event] with z hz_pull hz_eq
  have h_specialised :
      JacobianChallenge.cyclicSum (h ∘ φ) ω k (ψ z)
        = (ψ z) ^ (k - 1) * Q ((ψ z) ^ k) :=
    hz_pull (ψ z) rfl
  rw [h_specialised, ← hz_eq]

end Manifold
end JacobianChallenge
