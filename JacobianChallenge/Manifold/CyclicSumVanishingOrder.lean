/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CyclicSumZeroAtZero
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Constructions

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Vanishing-to-order-`(k-1)` of `cyclicSum` at `0`

For `h : ℂ → ℂ` analytic at `0` and `ω` a primitive `k`-th root of unity
with `k ≥ 2`, the cyclic sum

`S(ξ) := cyclicSum h ω k ξ = ∑_{j < k} ω^j · h(ω^j · ξ)`

vanishes to order at least `k - 1` at `ξ = 0`. Equivalently, there is an
analytic factor `q` with `S(ξ) = ξ^(k-1) · q(ξ)` in a neighbourhood of `0`.

## Proof outline

1. `S` is analytic at `0` (finite sum of compositions of analytic maps).
2. Case split on whether `S` is identically zero in a neighbourhood of `0`.
   * **Identically zero**: take `q := 0`.
   * **Not identically zero**: by `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`,
     there is `m : ℕ` and analytic `g` with `g(0) ≠ 0` and
     `S(ξ) = ξ^m · g(ξ)` for `ξ` near `0`.

     The symmetry `S(ωξ) = ω⁻¹ S(ξ)` (from `cyclicSum_omega_shift`) becomes
     `(ωξ)^m · g(ωξ) = ω⁻¹ · ξ^m · g(ξ)`, i.e., for `ξ ≠ 0` near `0`,
     `ω^m · g(ωξ) = ω⁻¹ · g(ξ)`. Continuity at `0` gives
     `(ω^m - ω⁻¹) · g(0) = 0`, and `g(0) ≠ 0` forces `ω^(m+1) = 1`.

     By `IsPrimitiveRoot`, `k ∣ m + 1`, so `m + 1 ≥ k`, hence `m ≥ k - 1`.
     Factor `ξ^m = ξ^(k-1) · ξ^(m - (k-1))`; take `q(ξ) := ξ^(m-(k-1)) · g(ξ)`.

## What this file ships

* `cyclicSum_analyticAt_zero` — analyticity of `cyclicSum h ω k` at `ξ = 0`.
* `cyclicSum_factor_pow_k_sub_one` — analytic factorisation
  `S(ξ) = ξ^(k-1) · q(ξ)` near `0`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge

/-- `cyclicSum h ω k` is analytic at `0` when `h` is. Each summand
`ξ ↦ ω^j · h(ω^j · ξ)` is the composition of an analytic linear map with
the analytic `h`, scaled by a constant. -/
theorem cyclicSum_analyticAt_zero
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (h_an : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (cyclicSum h ω k) 0 := by
  unfold cyclicSum
  apply Finset.analyticAt_fun_sum
  intro j _
  -- Need: AnalyticAt ℂ (fun ξ => ω^j * h (ω^j * ξ)) 0.
  have h_lin_an : AnalyticAt ℂ (fun ξ : ℂ => ω ^ j * ξ) 0 :=
    analyticAt_const.mul analyticAt_id
  have h_at_zero : (fun ξ : ℂ => ω ^ j * ξ) 0 = 0 := by simp
  have h_comp : AnalyticAt ℂ (fun ξ : ℂ => h (ω ^ j * ξ)) 0 :=
    h_an.comp_of_eq' h_lin_an h_at_zero
  exact analyticAt_const.mul h_comp

/-- **Vanishing to order `(k-1)`.** For analytic `h` at `0` and `ω` a primitive
`k`-th root of unity with `k ≥ 2`, there exists an analytic `q` with
`cyclicSum h ω k ξ = ξ^(k-1) · q(ξ)` in a neighbourhood of `0`.

This is the bound underlying the bounded-trace step of the
`HolomorphicTraceExtension X` item-(2) globalize: at each preimage of a
critical value with ramification index `k`, the cancellation produces a
factor `ξ^(1-k)` that is cancelled exactly by this vanishing of the cyclic
sum at the `k`-th-root substitution coordinate. -/
theorem cyclicSum_factor_pow_k_sub_one
    {h : ℂ → ℂ} {ω : ℂ} {k : ℕ} (hω : IsPrimitiveRoot ω k) (hk : 2 ≤ k)
    (h_an : AnalyticAt ℂ h 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ ξ in 𝓝 (0 : ℂ), cyclicSum h ω k ξ = ξ ^ (k - 1) * q ξ := by
  have hk_pos : 0 < k := by linarith
  -- Setup: ω ≠ 0 and ω ≠ 1.
  have hω_ne_zero : ω ≠ 0 := by
    intro h_zero
    have : (0 : ℂ) ^ k = 1 := by rw [← h_zero]; exact hω.pow_eq_one
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)] at this
    exact zero_ne_one this
  have hω_ne_one : ω ≠ 1 := hω.ne_one (by linarith)
  -- 1. cyclicSum is analytic at 0.
  have hS_an : AnalyticAt ℂ (cyclicSum h ω k) 0 :=
    cyclicSum_analyticAt_zero h_an
  -- 2. Case split: identically zero in a nbhd, or not.
  by_cases h_zero_nhd : ∀ᶠ ξ in 𝓝 (0 : ℂ), cyclicSum h ω k ξ = 0
  · -- Identically zero: take q := 0.
    refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [h_zero_nhd] with ξ hξ
    rw [hξ, mul_zero]
  · -- Not identically zero: get the order m via the AnalyticAt API.
    obtain ⟨m, g, g_an, g_ne, h_eq⟩ :=
      hS_an.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h_zero_nhd
    -- Simplify: (z - 0)^m • g z = z^m * g z.
    have h_eq' : ∀ᶠ ξ in 𝓝 (0 : ℂ), cyclicSum h ω k ξ = ξ ^ m * g ξ := by
      filter_upwards [h_eq] with ξ hξ
      rw [hξ]; rw [sub_zero, smul_eq_mul]
    -- 3. Symmetry + local form → for ξ ≠ 0 near 0, ω^m · g(ωξ) = ω⁻¹ · g(ξ).
    -- Pull h_eq' back along ξ ↦ ω*ξ (continuous at 0, sending 0 to 0).
    have h_mul_tendsto : Tendsto (fun ξ : ℂ => ω * ξ) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun ξ : ℂ => ω * ξ) (𝓝 0) (𝓝 (ω * 0)) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto
      simpa using this
    have h_eq_shift : ∀ᶠ ξ in 𝓝 (0 : ℂ),
        cyclicSum h ω k (ω * ξ) = (ω * ξ) ^ m * g (ω * ξ) :=
      h_mul_tendsto.eventually h_eq'
    -- Combine with the algebraic symmetry cyclicSum_omega_shift.
    have h_combined : ∀ᶠ ξ in 𝓝 (0 : ℂ),
        (ω * ξ) ^ m * g (ω * ξ) = ω⁻¹ * (ξ ^ m * g ξ) := by
      filter_upwards [h_eq_shift, h_eq'] with ξ hshift heq
      have h_sym := cyclicSum_omega_shift hω hk_pos h ξ
      rw [← hshift, h_sym, heq]
    -- Define P(ξ) := ω^m · g(ωξ) - ω⁻¹ · g(ξ). This is continuous at 0 (analytic).
    set P : ℂ → ℂ := fun ξ => ω ^ m * g (ω * ξ) - ω⁻¹ * g ξ with hP_def
    have hP_an : AnalyticAt ℂ P 0 := by
      have h_mul_an : AnalyticAt ℂ (fun ξ : ℂ => ω * ξ) 0 :=
        analyticAt_const.mul analyticAt_id
      have h_mul_zero : (fun ξ : ℂ => ω * ξ) 0 = 0 := by simp
      have h_g_comp : AnalyticAt ℂ (fun ξ : ℂ => g (ω * ξ)) 0 :=
        g_an.comp_of_eq' h_mul_an h_mul_zero
      have h_term1 : AnalyticAt ℂ (fun ξ : ℂ => ω ^ m * g (ω * ξ)) 0 :=
        analyticAt_const.mul h_g_comp
      have h_term2 : AnalyticAt ℂ (fun ξ : ℂ => ω⁻¹ * g ξ) 0 :=
        analyticAt_const.mul g_an
      exact h_term1.sub h_term2
    have hP_cont : ContinuousAt P 0 := hP_an.continuousAt
    -- For ξ ≠ 0 in a small ball around 0, h_combined gives ξ^m · P(ξ) = 0,
    -- hence P(ξ) = 0 (since ξ^m ≠ 0).
    have h_P_zero_punctured : ∀ᶠ ξ in 𝓝[≠] (0 : ℂ), P ξ = 0 := by
      have h_combined' : ∀ᶠ ξ in 𝓝[≠] (0 : ℂ),
          (ω * ξ) ^ m * g (ω * ξ) = ω⁻¹ * (ξ ^ m * g ξ) :=
        h_combined.filter_mono nhdsWithin_le_nhds
      filter_upwards [h_combined', self_mem_nhdsWithin] with ξ h_eq_at h_ne_zero
      have h_ne : ξ ∈ ({(0 : ℂ)} : Set ℂ)ᶜ := h_ne_zero
      have hξ_ne : ξ ≠ 0 := h_ne
      have hξm_ne : ξ ^ m ≠ 0 := pow_ne_zero m hξ_ne
      -- (ωξ)^m = ω^m · ξ^m.
      have h_lhs : (ω * ξ) ^ m * g (ω * ξ) = ω ^ m * ξ ^ m * g (ω * ξ) := by
        rw [mul_pow]
      rw [h_lhs] at h_eq_at
      -- ω^m · ξ^m · g(ωξ) = ω⁻¹ · (ξ^m · g ξ).
      -- Reassociate to factor ξ^m on the left, then cancel.
      have h_factor :
          ξ ^ m * (ω ^ m * g (ω * ξ)) = ξ ^ m * (ω⁻¹ * g ξ) := by
        linear_combination h_eq_at
      have h_can : ω ^ m * g (ω * ξ) = ω⁻¹ * g ξ :=
        mul_left_cancel₀ hξm_ne h_factor
      show ω ^ m * g (ω * ξ) - ω⁻¹ * g ξ = 0
      linear_combination h_can
    -- 4. Continuity at 0 → P(0) = 0.
    have hP_at_zero : P 0 = 0 := by
      -- Tendsto P (𝓝[≠] 0) (𝓝 0) from `P =ᶠ[𝓝[≠] 0] 0`.
      have h_P_eq_zero : P =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := h_P_zero_punctured
      have h_tendsto_zero : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
        (tendsto_congr' h_P_eq_zero).mpr tendsto_const_nhds
      -- Tendsto P (𝓝[≠] 0) (𝓝 (P 0)) from continuity.
      have h_tendsto_P0 : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 (P 0)) :=
        hP_cont.continuousWithinAt.tendsto
      -- Punctured nbhd is non-trivial in ℂ.
      haveI : NeBot (𝓝[≠] (0 : ℂ)) := inferInstance
      exact tendsto_nhds_unique h_tendsto_P0 h_tendsto_zero
    -- 5. P(0) = ω^m · g(0) - ω⁻¹ · g(0) = (ω^m - ω⁻¹) · g(0) = 0.
    -- Since g(0) ≠ 0, ω^m = ω⁻¹, i.e., ω^(m+1) = 1.
    have h_P0_expanded : P 0 = (ω ^ m - ω⁻¹) * g 0 := by
      show ω ^ m * g (ω * 0) - ω⁻¹ * g 0 = (ω ^ m - ω⁻¹) * g 0
      rw [mul_zero]; ring
    have h_factor_zero : (ω ^ m - ω⁻¹) * g 0 = 0 := by
      rw [← h_P0_expanded]; exact hP_at_zero
    have h_diff_zero : ω ^ m - ω⁻¹ = 0 :=
      (mul_eq_zero.mp h_factor_zero).resolve_right g_ne
    have h_pow_eq : ω ^ m = ω⁻¹ := sub_eq_zero.mp h_diff_zero
    have h_pow_succ : ω ^ (m + 1) = 1 := by
      rw [pow_succ, h_pow_eq, inv_mul_cancel₀ hω_ne_zero]
    -- 6. k ∣ m + 1 → m + 1 ≥ k → m ≥ k - 1.
    have h_k_dvd : k ∣ (m + 1) := (hω.pow_eq_one_iff_dvd (m + 1)).mp h_pow_succ
    have h_m_succ_pos : 0 < m + 1 := Nat.succ_pos m
    have h_m_succ_ge : k ≤ m + 1 := Nat.le_of_dvd h_m_succ_pos h_k_dvd
    have h_m_ge : k - 1 ≤ m := by omega
    -- 7. Construct q.
    set r : ℕ := m - (k - 1) with hr_def
    have h_m_decomp : m = (k - 1) + r := by omega
    refine ⟨fun ξ => ξ ^ r * g ξ, ?_, ?_⟩
    · exact (analyticAt_id.pow _).mul g_an
    · filter_upwards [h_eq'] with ξ hξ
      rw [hξ]
      -- ξ^m * g ξ = ξ^(k-1) * (ξ^r * g ξ).
      rw [h_m_decomp, pow_add]
      ring

end JacobianChallenge
