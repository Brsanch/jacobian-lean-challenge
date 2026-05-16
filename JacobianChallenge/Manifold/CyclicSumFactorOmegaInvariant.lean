/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumVanishingOrder

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # The factor `q` in `cyclicSum = ξ^(k-1) · q` is `ω`-invariant

Strengthening of `cyclicSum_factor_pow_k_sub_one`: the analytic factor `q`
satisfies `q(ω · ξ) = q(ξ)` near `0`. Direct consequence of the
cyclic-sum symmetry `cyclicSum(ωξ) = ω⁻¹ · cyclicSum(ξ)`:

`(ωξ)^(k-1) · q(ωξ) = ω⁻¹ · ξ^(k-1) · q(ξ)`
`ω^(k-1) · ξ^(k-1) · q(ωξ) = ω^(-1) · ξ^(k-1) · q(ξ)`

For `ξ ≠ 0` near `0`: cancel `ξ^(k-1)` to get `ω^k · q(ωξ) = q(ξ)`, i.e.,
`q(ωξ) = q(ξ)` (since `ω^k = 1`). For `ξ = 0`: trivially `q(0) = q(0)`.
Continuity extension fills in `ξ = 0`.

This sets up the **descent** of `q` to a function of `ξ^k`: by Taylor
expansion, an `ω`-invariant analytic function has only Taylor coefficients
at exponents divisible by `k`, hence factors as `q(ξ) = Q(ξ^k)` for some
analytic `Q`. Combined with `cyclicSum = ξ^(k-1) · q = ξ^(k-1) · Q(ξ^k)`
and the manifold-side wiring at a critical preimage of `f : X → ℙ¹`, this
produces a trace 1-form on the target that is *analytic in the target
coordinate* (not merely in the `k`-th-root variable). -/

open Filter Topology

namespace JacobianChallenge

/-- **The analytic factor in `cyclicSum = ξ^(k-1) · q` is `ω`-invariant.**
The same `q` as in `cyclicSum_factor_pow_k_sub_one`, augmented with the
additional invariance `q(ω · ξ) = q(ξ)` in a neighbourhood of `0`. -/
theorem cyclicSum_factor_pow_k_sub_one_omega_invariant
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 2 ≤ k)
    (h_an : AnalyticAt ℂ h 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ), cyclicSum h ω k ξ = ξ ^ (k - 1) * q ξ) ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ), q (ω * ξ) = q ξ) := by
  obtain ⟨q, q_an, h_eq⟩ := cyclicSum_factor_pow_k_sub_one hω hk h_an
  refine ⟨q, q_an, h_eq, ?_⟩
  have hk_pos : 0 < k := by linarith
  have hω_ne_zero : ω ≠ 0 := by
    intro h_zero
    have : (0 : ℂ) ^ k = 1 := by rw [← h_zero]; exact hω.pow_eq_one
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)] at this
    exact zero_ne_one this
  have hω_pow_k : ω ^ k = 1 := hω.pow_eq_one
  -- Pull h_eq back along ξ ↦ ω·ξ.
  have h_mul_tendsto : Tendsto (fun ξ : ℂ => ω * ξ) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun ξ : ℂ => ω * ξ) (𝓝 0) (𝓝 (ω * 0)) :=
      (continuous_const.mul continuous_id).continuousAt.tendsto
    simpa using this
  have h_eq_shift : ∀ᶠ ξ in 𝓝 (0 : ℂ),
      cyclicSum h ω k (ω * ξ) = (ω * ξ) ^ (k - 1) * q (ω * ξ) :=
    h_mul_tendsto.eventually h_eq
  -- Combine with the algebraic symmetry and the original factorisation.
  -- For ξ near 0 (in particular ξ ≠ 0): ω^(k-1) · q(ωξ) = ω⁻¹ · q(ξ), i.e.,
  -- q(ωξ) = ω⁻k · q(ξ) = q(ξ).
  set P : ℂ → ℂ := fun ξ => q (ω * ξ) - q ξ with hP_def
  have hP_an : AnalyticAt ℂ P 0 := by
    have h_mul_an : AnalyticAt ℂ (fun ξ : ℂ => ω * ξ) 0 :=
      analyticAt_const.mul analyticAt_id
    have h_mul_zero : (fun ξ : ℂ => ω * ξ) 0 = 0 := by simp
    have h_q_comp : AnalyticAt ℂ (fun ξ : ℂ => q (ω * ξ)) 0 :=
      q_an.comp_of_eq' h_mul_an h_mul_zero
    exact h_q_comp.sub q_an
  have hP_cont : ContinuousAt P 0 := hP_an.continuousAt
  -- For ξ ≠ 0 near 0, P ξ = 0.
  have h_P_zero_punctured : ∀ᶠ ξ in 𝓝[≠] (0 : ℂ), P ξ = 0 := by
    have h_combined :
        ∀ᶠ ξ in 𝓝 (0 : ℂ),
          ξ ^ (k - 1) * q ξ = cyclicSum h ω k ξ ∧
          (ω * ξ) ^ (k - 1) * q (ω * ξ) = cyclicSum h ω k (ω * ξ) := by
      filter_upwards [h_eq, h_eq_shift] with ξ h1 h2
      exact ⟨h1.symm, h2.symm⟩
    have h_combined' : ∀ᶠ ξ in 𝓝[≠] (0 : ℂ),
        ξ ^ (k - 1) * q ξ = cyclicSum h ω k ξ ∧
        (ω * ξ) ^ (k - 1) * q (ω * ξ) = cyclicSum h ω k (ω * ξ) :=
      h_combined.filter_mono nhdsWithin_le_nhds
    filter_upwards [h_combined', self_mem_nhdsWithin] with ξ ⟨h_eq1, h_eq2⟩ h_ne
    have hξ_ne : ξ ≠ 0 := h_ne
    have h_k_minus_one_pos : 0 < k - 1 := by omega
    have hξpow_ne : ξ ^ (k - 1) ≠ 0 := pow_ne_zero _ hξ_ne
    have h_sym := cyclicSum_omega_shift hω hk_pos h ξ
    -- (ωξ)^(k-1) · q(ωξ) = cyclicSum(ωξ) = ω⁻¹ · cyclicSum(ξ) = ω⁻¹ · ξ^(k-1) · q(ξ).
    have h_chain :
        (ω * ξ) ^ (k - 1) * q (ω * ξ) = ω⁻¹ * (ξ ^ (k - 1) * q ξ) := by
      rw [h_eq2, h_sym, h_eq1]
    -- Expand (ωξ)^(k-1) = ω^(k-1) · ξ^(k-1).
    have h_expand : (ω * ξ) ^ (k - 1) = ω ^ (k - 1) * ξ ^ (k - 1) := by
      rw [mul_pow]
    rw [h_expand] at h_chain
    -- ω^(k-1) · ξ^(k-1) · q(ωξ) = ω⁻¹ · ξ^(k-1) · q(ξ).
    -- Reassociate to ξ^(k-1) · (ω^(k-1) · q(ωξ)) = ξ^(k-1) · (ω⁻¹ · q(ξ)).
    have h_assoc :
        ξ ^ (k - 1) * (ω ^ (k - 1) * q (ω * ξ)) =
          ξ ^ (k - 1) * (ω⁻¹ * q ξ) := by
      linear_combination h_chain
    have h_can : ω ^ (k - 1) * q (ω * ξ) = ω⁻¹ * q ξ :=
      mul_left_cancel₀ hξpow_ne h_assoc
    -- Multiply both sides by ω to get ω^k · q(ωξ) = q(ξ).
    have h_mul_omega :
        ω * (ω ^ (k - 1) * q (ω * ξ)) = ω * (ω⁻¹ * q ξ) := by
      rw [h_can]
    have h_left :
        ω * (ω ^ (k - 1) * q (ω * ξ)) = ω ^ k * q (ω * ξ) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk_pos]
    have h_right : ω * (ω⁻¹ * q ξ) = q ξ := by
      rw [← mul_assoc, mul_inv_cancel₀ hω_ne_zero, one_mul]
    rw [h_left, h_right, hω_pow_k, one_mul] at h_mul_omega
    -- h_mul_omega : q (ω * ξ) = q ξ.
    show q (ω * ξ) - q ξ = 0
    linear_combination h_mul_omega
  -- Continuity at 0: P(0) = 0 since P = 0 on 𝓝[≠] 0.
  have hP_at_zero : P 0 = 0 := by
    have h_P_eq_zero : P =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := h_P_zero_punctured
    have h_tendsto_zero : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      (tendsto_congr' h_P_eq_zero).mpr tendsto_const_nhds
    have h_tendsto_P0 : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 (P 0)) :=
      hP_cont.continuousWithinAt.tendsto
    haveI : NeBot (𝓝[≠] (0 : ℂ)) := inferInstance
    exact tendsto_nhds_unique h_tendsto_P0 h_tendsto_zero
  -- Upgrade P = 0 on 𝓝[≠] 0 + P 0 = 0 → P = 0 on 𝓝 0.
  -- Extract the underlying open neighbourhood and check the value at 0 separately.
  rw [eventually_nhdsWithin_iff] at h_P_zero_punctured
  have h_P_zero_full : ∀ᶠ ξ in 𝓝 (0 : ℂ), P ξ = 0 := by
    filter_upwards [h_P_zero_punctured] with ξ h_imp
    by_cases hξ : ξ = 0
    · rw [hξ]; exact hP_at_zero
    · exact h_imp hξ
  -- Convert P ξ = 0 to q(ω·ξ) = q(ξ).
  filter_upwards [h_P_zero_full] with ξ hξ
  show q (ω * ξ) = q ξ
  have h_diff : q (ω * ξ) - q ξ = 0 := hξ
  linear_combination h_diff

end JacobianChallenge
