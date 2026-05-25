/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelDCTLimitRadial
import JacobianChallenge.Analysis.PompeiuKernelPartialZBarBridge
import JacobianChallenge.Analysis.PompeiuKernelRadialSubstitution
import JacobianChallenge.Analysis.PompeiuKernelSubstitutedDCT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-4: final identity

The unconditional Cauchy-Pompeiu identity on ℂ for `C¹`-functions with
compact support:

```
∀ α : ℂ → ℂ, ContDiff ℝ 1 α → HasCompactSupport α →
  ∀ z : ℂ, partialZBar (pompeiuKernel α) z = α z.
```

Proof: combine the balance equation `balance_plane_eq_zero_radial`
(Chip 3c-F-3c, Section B) at every `ε > 0` with the two ε-limits:
the first summand limit (Chip 3c-F-3c, Section C —
`tendsto_integral_partialZBar_alpha_mul_regInvSubRadial`) and the
substituted second-summand limit (Chip 3c-F-3d-2c
`integral_alpha_mul_partialZBar_regInvSubRadial_eq_substituted` +
Chip 3c-F-3d-3 `tendsto_integral_alpha_substituted`). Both limits exist
and sum to zero by linearity of the integral and the balance equation.
That gives `∫ ζ, ∂̄α(ζ) · (ζ-z)⁻¹ = -π · α(z)`, which combined with the
definition `pompeiuKernel α z := -(π⁻¹) · ∫ ζ, α(ζ) · (ζ-z)⁻¹` and
Chip 3b's bridge
(`partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar`) yields the
final identity.

This closes the Pompeiu kernel arc on ℂ. The remaining work for Item 14
(genus-0 globalization, chart pull-back, composition) is in Chips 4-7.

All sorry-free, axiom-free. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

variable {α : ℂ → ℂ}

/-! ## First summand limit, stripped of the `Real`-wrapper -/

/-- The first-summand DCT limit (Chip 3c-F-3c) reformulated with
`regularizedInvSubRadial` (no `Real`-wrapper) for ε in the right
neighborhood of `0`. -/
lemma tendsto_integral_partialZBar_alpha_mul_regInvSubRadial_unwrapped
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Tendsto (fun ε : ℝ =>
        ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹)) := by
  have h_main := tendsto_integral_partialZBar_alpha_mul_regInvSubRadial
                  h_smooth h_supp z
  -- For ε > 0, `regularizedInvSubRadialReal z ε = regularizedInvSubRadial z ε`.
  have h_eq :
      (fun ε : ℝ => ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadialReal z ε ζ)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε' : 0 < ε := hε_pos
    rw [regularizedInvSubRadialReal_of_pos hε']
  exact h_main.congr' h_eq

/-! ## Second summand limit -/

/-- The second-summand limit: as `ε → 0⁺`,
```
∫ ζ : ℂ, α(ζ) · partialZBar (regularizedInvSubRadial z ε) ζ
  → α(z) · π.
```

Combines Chip 3c-F-3d-2c's substitution identity with Chip 3c-F-3d-3's
DCT on the substituted integral; the final sign comes from
`(-x)·(-y) = x·y` on `α(z) · (-π)`. -/
lemma tendsto_integral_alpha_mul_partialZBar_regInvSubRadial
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Tendsto (fun ε : ℝ =>
        ∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (α z * ((Real.pi : ℝ) : ℂ))) := by
  have h_cont : Continuous α := h_smooth.continuous
  -- DCT on the substituted form (limit value α z · (-π : ℂ)).
  have h_subst := tendsto_integral_alpha_substituted h_cont h_supp z
  -- Negate both sides: -∫ → -(α z · (-π)) = α z · π.
  have h_neg := h_subst.neg
  -- Rewrite the limit value as `α z * π`.
  have h_target_eq : -(α z * ((-Real.pi : ℝ) : ℂ)) = α z * ((Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  rw [h_target_eq] at h_neg
  -- For ε > 0, Chip 3c-F-3d-2c gives the substitution identity. The
  -- second-summand integral equals `-∫ w, α(z + εw) · ∂̄(unitRadialBumpC)/w`.
  -- So the two function-of-ε agree eventually.
  have h_eq :
      (fun ε : ℝ =>
          -∫ w : ℂ, α (z + (ε : ℂ) * w) *
            (partialZBar unitRadialBumpC w / w))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ =>
          ∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε' : 0 < ε := hε_pos
    have h_id :=
      integral_alpha_mul_partialZBar_regInvSubRadial_eq_substituted α (z := z) hε'
    -- h_id : ∫ ζ, α · ∂̄(regInvSubRadial z ε) = -∫ w, α(z+εw) · ∂̄(unitRadialBumpC)/w
    exact h_id.symm
  exact h_neg.congr' h_eq

/-! ## Combining: sum of the two limits is zero -/

/-- For every `ε > 0`, the sum of the two summand integrals is zero
(`balance_plane_eq_zero_radial` after splitting `integral_add`). -/
lemma sum_summand_integrals_eq_zero
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ)
      + (∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ) = 0 := by
  -- Need an L > 0 with tsupport α ⊆ ball 0 L to invoke balance_plane_eq_zero_radial.
  obtain ⟨L, hL_pos, hL_supp⟩ :=
    h_supp.isBounded.subset_ball_lt 0 (0 : ℂ)
  have h_sum := balance_plane_eq_zero_radial h_smooth h_supp z hε hL_pos hL_supp
  -- Split the integral.
  have h_int_first :=
    integrable_partialZBar_mul_regInvSubRadial h_smooth h_supp z hε
  have h_int_second :=
    integrable_alpha_mul_partialZBar_regInvSubRadial h_smooth h_supp z hε
  rw [integral_add h_int_first h_int_second] at h_sum
  exact h_sum

/-- The integral `∫ ζ, ∂̄α(ζ) · (ζ - z)⁻¹` equals `-π · α(z)`. -/
theorem integral_partialZBar_alpha_mul_inv_sub_eq_neg_pi_mul
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹)
      = ((-Real.pi : ℝ) : ℂ) * α z := by
  -- Each ε > 0: A(ε) + B(ε) = 0.
  -- A(ε) → ∫ ∂̄α · (ζ-z)⁻¹ (h_A).
  -- B(ε) → α z · π (h_B).
  -- Sum: ∫ ∂̄α · (ζ-z)⁻¹ + α z · π = 0.
  have h_A := tendsto_integral_partialZBar_alpha_mul_regInvSubRadial_unwrapped
                h_smooth h_supp z
  have h_B := tendsto_integral_alpha_mul_partialZBar_regInvSubRadial
                h_smooth h_supp z
  have h_sum := h_A.add h_B
  -- Constant zero limit from the balance.
  have h_const_zero :
      (fun ε : ℝ =>
          (∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ)
            + (∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    exact sum_summand_integrals_eq_zero h_smooth h_supp z hε_pos
  have h_lim_zero :
      Tendsto (fun ε : ℝ =>
          (∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ)
            + (∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    exact (tendsto_const_nhds).congr' h_const_zero.symm
  -- Uniqueness of limits in a T2 space.
  have h_sum_eq_zero :
      (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹) + α z * ((Real.pi : ℝ) : ℂ) = 0 :=
    tendsto_nhds_unique h_sum h_lim_zero
  -- Solve for the first summand.
  have : (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹) = -(α z * ((Real.pi : ℝ) : ℂ)) := by
    linear_combination h_sum_eq_zero
  rw [this]
  push_cast
  ring

/-! ## Final identity: `partialZBar (pompeiuKernel α) z = α z` -/

/-- **Chip 3c-F-4 — final Cauchy-Pompeiu identity on ℂ.** For every
`C¹`-function with compact support `α : ℂ → ℂ`, the Pompeiu kernel is a
right inverse to `∂̄`:

```
partialZBar (pompeiuKernel α) z = α z.
```

Proof: Chip 3b reduces the LHS to `pompeiuKernel (partialZBar α) z`. By
definition of `pompeiuKernel`, this is `-(π⁻¹) · ∫ ζ, ∂̄α(ζ) · (ζ-z)⁻¹`,
and the integral equals `-π · α(z)` by
`integral_partialZBar_alpha_mul_inv_sub_eq_neg_pi_mul`. The factors of
`-π · -π⁻¹` cancel to `1` (using `π ≠ 0`). -/
theorem partialZBar_pompeiuKernel_eq_self
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    partialZBar (pompeiuKernel α) z = α z := by
  rw [partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar h_smooth h_supp z]
  -- Now: pompeiuKernel (partialZBar α) z = α z.
  unfold pompeiuKernel
  -- = -(π⁻¹ : ℂ) · ∫ ζ, ∂̄α(ζ) · (ζ-z)⁻¹  (via pompeiuIntegrand def).
  have h_int_eq :
      (∫ ζ : ℂ, pompeiuIntegrand (partialZBar α) z ζ)
        = ((-Real.pi : ℝ) : ℂ) * α z := by
    show (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹) = _
    exact integral_partialZBar_alpha_mul_inv_sub_eq_neg_pi_mul h_smooth h_supp z
  rw [h_int_eq]
  have hπ_C_ne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  -- -(π⁻¹) · (-π · α z) = α z.
  push_cast
  field_simp

end JacobianChallenge.PompeiuKernel
