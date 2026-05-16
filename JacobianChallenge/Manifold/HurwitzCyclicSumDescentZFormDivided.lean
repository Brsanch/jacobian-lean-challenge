/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCyclicSumDescentKthRoot
import JacobianChallenge.Manifold.HurwitzZetaLocalNonzero

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Divided form of the source-side z-form cyclic-sum descent

Combines the kth-root form (chip 3c-4) with the local non-vanishing
`ψ z ≠ 0` for `z ≠ x₀` near `x₀` (chip 3c-6) to produce the
**divided form** of the source-side z-form descent:

  `cyclicSum (h ∘ φ) ω k (ψ z) / ((↑k) · (ψ z)^(k-1)) = Q(g z - w₀) / ↑k`

for `z ≠ x₀` near `x₀`.

This is the chart-coefficient form of the trace 1-form `f_*α` near a
critical value `w₀`: the LHS is the source-fibre cyclic-sum trace
normalised by `k · (ψ z)^(k-1)` (which equals the chart-coefficient
of `holTraceAt` at the target value, via the local k-fold cover);
the RHS is `Q(g z - w₀) / k`, manifestly analytic across `w₀`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Divided form of the source-side z-form descent.**

For `g, h : ℂ → ℂ` analytic at `x₀`, `analyticOrderAt (g - w₀) x₀ = k`
(`k ≥ 2`), primitive k-th root `ω`, produces ψ, φ, Q with the divided
identity in `z` near `x₀`, `z ≠ x₀`:

  `cyclicSum (h ∘ φ) ω k (ψ z) / ((↑k) * (ψ z)^(k-1)) = Q (g z - w₀) / ↑k`. -/
theorem hurwitz_cyclic_sum_descent_zForm_divided
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
      (∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
        JacobianChallenge.cyclicSum (h ∘ φ) ω k (ψ z)
            / ((k : ℂ) * (ψ z) ^ (k - 1))
          = Q (g z - w₀) / (k : ℂ)) := by
  -- Step 1. Apply the kth-root form (chip 3c-4), which exposes `h_left`.
  obtain ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          _h_right, h_left, Q_an, h_v_form⟩ :=
    hurwitz_cyclic_sum_descent_kthRoot_form hk hg h_w₀ hord h_an hω
  -- Step 2. Derive the z-form identity (same calculation as chip 3c-5).
  have hψ_at_x₀ : AnalyticAt ℂ ψ x₀ :=
    hψ_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  have hψ_cont : ContinuousAt ψ x₀ := hψ_at_x₀.continuousAt
  have hψ_tendsto : Tendsto ψ (𝓝 x₀) (𝓝 0) := by
    have h_to_ψx₀ : Tendsto ψ (𝓝 x₀) (𝓝 (ψ x₀)) := hψ_cont.tendsto
    simpa [hψ_x₀] using h_to_ψx₀
  have h_pulled : ∀ᶠ z in 𝓝 x₀, ∀ ξ : ℂ, ξ ^ k = (ψ z) ^ k →
      JacobianChallenge.cyclicSum (h ∘ φ) ω k ξ
        = ξ ^ (k - 1) * Q ((ψ z) ^ k) := by
    have h_pow_tendsto : Tendsto (fun z => (ψ z) ^ k) (𝓝 x₀) (𝓝 0) := by
      have : Tendsto (fun z => (ψ z) ^ k) (𝓝 x₀) (𝓝 ((0 : ℂ) ^ k)) :=
        hψ_tendsto.pow k
      have hk_ne : k ≠ 0 := by omega
      simpa [zero_pow hk_ne] using this
    exact h_pow_tendsto.eventually h_v_form
  have h_eq_event : ∀ᶠ z in 𝓝 x₀, g z - w₀ = (ψ z) ^ k := by
    have hball_nhds : Metric.closedBall x₀ R ∈ 𝓝 x₀ :=
      Metric.closedBall_mem_nhds x₀ hR_pos
    filter_upwards [hball_nhds] with z hz
    exact h_fact z hz
  have h_z_form : ∀ᶠ z in 𝓝 x₀,
      JacobianChallenge.cyclicSum (h ∘ φ) ω k (ψ z)
        = (ψ z) ^ (k - 1) * Q (g z - w₀) := by
    filter_upwards [h_pulled, h_eq_event] with z hz_pull hz_eq
    have h_specialised :
        JacobianChallenge.cyclicSum (h ∘ φ) ω k (ψ z)
          = (ψ z) ^ (k - 1) * Q ((ψ z) ^ k) := hz_pull (ψ z) rfl
    rw [h_specialised, ← hz_eq]
  -- Step 3. Get `ψ z ≠ 0` for z ≠ x₀ near x₀.
  have h_nz : ∀ᶠ z in 𝓝 x₀, z ≠ x₀ → ψ z ≠ 0 :=
    hurwitz_ne_zero_of_ne_x₀ hψ_x₀ h_left
  -- Step 4. Combine.
  have hk_ne_ℂ : (k : ℂ) ≠ 0 := by
    have hk_ne : k ≠ 0 := by omega
    exact_mod_cast hk_ne
  refine ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          Q_an, ?_⟩
  filter_upwards [h_z_form, h_nz] with z h_eq h_imp hne
  have hψz_ne : ψ z ≠ 0 := h_imp hne
  have hpow_ne : (ψ z) ^ (k - 1) ≠ 0 := pow_ne_zero _ hψz_ne
  have h_denom_ne : (k : ℂ) * (ψ z) ^ (k - 1) ≠ 0 := mul_ne_zero hk_ne_ℂ hpow_ne
  -- From `cyclicSum = ξ^(k-1) · Q v`, divide both sides by `k · ξ^(k-1)`:
  -- LHS / (k · ξ^{k-1}) = (ξ^(k-1) · Q v) / (k · ξ^(k-1)) = Q v / k.
  rw [h_eq]
  field_simp

end Manifold
end JacobianChallenge
