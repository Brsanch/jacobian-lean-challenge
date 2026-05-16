/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumVanishingOrder

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Quantitative bound `|cyclicSum| ≤ C · |ξ|^(k-1)` near `0`

Corollary of `cyclicSum_factor_pow_k_sub_one`: for analytic `h` and ω
primitive `k`-th root with `k ≥ 2`, there exist `C, ρ > 0` such that

`‖cyclicSum h ω k ξ‖ ≤ C · ‖ξ‖^(k-1)`   for `‖ξ‖ ≤ ρ`.

Proof: from the analytic factorisation `cyclicSum = ξ^(k-1) · q` with `q`
analytic, hence continuous at `0`, we get `‖q ξ‖ ≤ ‖q 0‖ + 1` on a small
ball. Then `‖cyclicSum ξ‖ = ‖ξ‖^(k-1) · ‖q ξ‖ ≤ (‖q 0‖ + 1) · ‖ξ‖^(k-1)`.

This is the bound that, applied at each preimage of a critical value `v₀`
with ramification index `k`, cancels the `ξ^{1-k}` factor in the per-sheet
trace contribution, producing a continuous extension of the trace 1-form
across `v₀`. -/

open Filter Topology

namespace JacobianChallenge

/-- **Bounded-trace bound.** For analytic `h` at `0` and `ω` a primitive
`k`-th root of unity with `k ≥ 2`, there exist `C ρ > 0` with
`‖cyclicSum h ω k ξ‖ ≤ C · ‖ξ‖^(k-1)` for `‖ξ‖ ≤ ρ`. -/
theorem cyclicSum_norm_bounded
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 2 ≤ k)
    (h_an : AnalyticAt ℂ h 0) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧
      ∀ ξ : ℂ, ‖ξ‖ ≤ ρ → ‖cyclicSum h ω k ξ‖ ≤ C * ‖ξ‖ ^ (k - 1) := by
  obtain ⟨q, q_an, h_eq⟩ := cyclicSum_factor_pow_k_sub_one hω hk h_an
  -- C := ‖q 0‖ + 1.
  let C : ℝ := ‖q 0‖ + 1
  have hC_pos : 0 < C := by
    show 0 < ‖q 0‖ + 1
    have : 0 ≤ ‖q 0‖ := norm_nonneg _
    linarith
  -- q is continuous at 0, so ‖q ξ‖ ≤ C on a nbhd of 0.
  have hq_cont : ContinuousAt q 0 := q_an.continuousAt
  have hq_tendsto : Tendsto q (𝓝 0) (𝓝 (q 0)) := hq_cont.tendsto
  have hq_local_bound : ∀ᶠ ξ in 𝓝 (0 : ℂ), ‖q ξ - q 0‖ < 1 := by
    have : ∀ᶠ ξ in 𝓝 (0 : ℂ), dist (q ξ) (q 0) < 1 :=
      Metric.tendsto_nhds.mp hq_tendsto 1 one_pos
    simpa [dist_eq_norm] using this
  -- Combine eventual statements: factorisation + bound on ‖q‖.
  have h_combined : ∀ᶠ ξ in 𝓝 (0 : ℂ),
      cyclicSum h ω k ξ = ξ ^ (k - 1) * q ξ ∧ ‖q ξ‖ ≤ C := by
    filter_upwards [h_eq, hq_local_bound] with ξ h1 h2
    refine ⟨h1, ?_⟩
    -- ‖q ξ‖ ≤ ‖q ξ - q 0‖ + ‖q 0‖ ≤ 1 + ‖q 0‖ = C.
    calc ‖q ξ‖
        = ‖q ξ - q 0 + q 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖q ξ - q 0‖ + ‖q 0‖ := norm_add_le _ _
      _ ≤ 1 + ‖q 0‖ := by linarith [h2.le]
      _ = C := by show 1 + ‖q 0‖ = ‖q 0‖ + 1; ring
  -- Extract a ball from the eventual statement.
  rw [Metric.eventually_nhds_iff] at h_combined
  obtain ⟨ε, hε_pos, h_ball⟩ := h_combined
  refine ⟨C, ε / 2, hC_pos, by linarith, ?_⟩
  intro ξ hξ_le
  -- ξ ∈ Metric.ball 0 ε.
  have hξ_lt : dist ξ 0 < ε := by
    rw [dist_zero_right]
    have : ‖ξ‖ < ε := by linarith
    exact this
  obtain ⟨hξ_eq, hq_le⟩ := h_ball hξ_lt
  rw [hξ_eq]
  -- ‖ξ^(k-1) * q ξ‖ = ‖ξ‖^(k-1) * ‖q ξ‖ ≤ ‖ξ‖^(k-1) * C = C * ‖ξ‖^(k-1).
  rw [norm_mul, norm_pow]
  have hξ_nn : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hpow_nn : 0 ≤ ‖ξ‖ ^ (k - 1) := pow_nonneg hξ_nn _
  calc ‖ξ‖ ^ (k - 1) * ‖q ξ‖
      ≤ ‖ξ‖ ^ (k - 1) * C := by exact mul_le_mul_of_nonneg_left hq_le hpow_nn
    _ = C * ‖ξ‖ ^ (k - 1) := by ring

end JacobianChallenge
