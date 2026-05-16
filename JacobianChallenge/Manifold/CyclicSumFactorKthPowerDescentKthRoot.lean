/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumFactorKthPowerDescent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Re-quantification of the cyclic-sum descent over target-side `v`

`CyclicSumFactorKthPowerDescent.lean` gives, for analytic `h : ℂ → ℂ` at
`0` and `ω` a primitive `k`-th root of unity (`k ≥ 2`), an analytic
`Q : ℂ → ℂ` at `0` with

  `∀ᶠ ξ in 𝓝 0, cyclicSum h ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)`.

This file re-quantifies over the target variable `v = ξ ^ k`:

  `∀ᶠ v in 𝓝 0, ∀ ξ : ℂ, ξ ^ k = v →
      cyclicSum h ω k ξ = ξ ^ (k - 1) * Q v`.

The translation uses that for `k ≥ 1` and any neighbourhood `U ∋ 0`, the
set `{v : ∀ ξ, ξ ^ k = v → ξ ∈ U}` is itself a neighbourhood of `0`
(because `ξ ↦ ξ ^ k` is open at `0`: the preimage of a small ball is
a small ball).

This form is the bridge between the source-side cyclic-sum (which lives
near the critical fibre point `ξ = 0`) and the target-side chart
coefficient of the trace 1-form (which lives near the critical value
`v = 0`). Downstream chips will combine this with the local k-fold form
of `f` at a critical fibre point to identify the chart coefficient of
the trace 1-form with `Q (·) / k` near a critical value.

No `sorry`, no `axiom`. -/

open Filter Topology Metric

namespace JacobianChallenge

/-- For `k ≥ 1` and any neighbourhood `U ∋ 0` of `0` in `ℂ`, every
sufficiently small `v` has the property that every `k`-th root of `v`
lies in `U`. The radius is `r ^ k` if `Metric.ball 0 r ⊆ U`.

This is the "openness of `ξ ↦ ξ ^ k` at `0`" packaged as a target-side
eventual statement. -/
theorem eventually_forall_pow_kth_root_mem_of_mem_nhds
    {k : ℕ} (hk : 1 ≤ k) {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) :
    ∀ᶠ v in 𝓝 (0 : ℂ), ∀ ξ : ℂ, ξ ^ k = v → ξ ∈ U := by
  -- Choose a metric ball inside `U`.
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp hU
  -- Target-side radius is `r ^ k`.
  refine Metric.eventually_nhds_iff.mpr ⟨r ^ k, by positivity, ?_⟩
  intro v hv ξ hξ_pow
  -- `‖v‖ < r ^ k`, and `ξ ^ k = v`. Need `ξ ∈ U`.
  -- It suffices to show `‖ξ‖ < r`, i.e. `ξ ∈ Metric.ball 0 r ⊆ U`.
  refine hr_sub ?_
  rw [Metric.mem_ball, dist_zero_right]
  have h_norm_pow : ‖ξ‖ ^ k = ‖v‖ := by
    rw [← norm_pow, hξ_pow]
  have h_dist : ‖v‖ < r ^ k := by
    have := hv
    rwa [dist_zero_right] at this
  -- Strict monotonicity of `x ↦ x ^ k` on `[0, ∞)` for `k ≥ 1`.
  have h_ξ_pow_lt : ‖ξ‖ ^ k < r ^ k := by rw [h_norm_pow]; exact h_dist
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  exact lt_of_pow_lt_pow_left₀ k (le_of_lt hr_pos) h_ξ_pow_lt

/-- **Descent of the cyclic-sum factor — target-side form.**

For `h : ℂ → ℂ` analytic at `0` and `ω` a primitive `k`-th root of
unity with `k ≥ 2`, there is an analytic `Q : ℂ → ℂ` at `0` such that
for all `v` near `0` and every `k`-th root `ξ` of `v`,

  `cyclicSum h ω k ξ = ξ ^ (k - 1) * Q v`.

Direct re-quantification of `cyclicSum_factor_descends_to_kth_power`
via the openness of `ξ ↦ ξ ^ k` at `0`. -/
theorem cyclicSum_factor_descends_kthRoot_form
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 2 ≤ k)
    (h_an : AnalyticAt ℂ h 0) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧
      (∀ᶠ v in 𝓝 (0 : ℂ), ∀ ξ : ℂ, ξ ^ k = v →
        cyclicSum h ω k ξ = ξ ^ (k - 1) * Q v) := by
  obtain ⟨Q, Q_an, h_eq_ξ⟩ :=
    cyclicSum_factor_descends_to_kth_power hω hk h_an
  refine ⟨Q, Q_an, ?_⟩
  -- Extract a nbhd `U` on which the source-side identity holds.
  rcases (Filter.eventually_iff_exists_mem.mp h_eq_ξ) with ⟨U, hU_nhds, hU_holds⟩
  have hk_pos : 1 ≤ k := by omega
  have h_pow_event : ∀ᶠ v in 𝓝 (0 : ℂ), ∀ ξ : ℂ, ξ ^ k = v → ξ ∈ U :=
    eventually_forall_pow_kth_root_mem_of_mem_nhds hk_pos hU_nhds
  filter_upwards [h_pow_event] with v hv ξ hξ_pow
  -- `ξ ∈ U`, so source-side identity gives `cyclicSum h ω k ξ = ξ^(k-1) * Q (ξ^k)`.
  have h_src := hU_holds ξ (hv ξ hξ_pow)
  rw [hξ_pow] at h_src
  exact h_src

end JacobianChallenge
