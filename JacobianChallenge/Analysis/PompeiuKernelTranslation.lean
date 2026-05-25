/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernel
import JacobianChallenge.Analysis.PompeiuIntegrandIntegrability
import Mathlib.MeasureTheory.Group.Integral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Chip 2a: translation reduction for the Pompeiu kernel

By translation invariance of Lebesgue measure on `ℂ`, the Pompeiu kernel
can be rewritten with the singularity pinned at `η = 0`:

  `pompeiuKernel α z = -(π⁻¹) · ∫ η, α (η + z) · η⁻¹`

This factors the `z`-dependence out of the singular `(ζ - z)⁻¹` factor
and into the `α (η + z)` factor — the key prerequisite for
differentiating `pompeiuKernel α` under the integral with respect to
`z` (Chip 2b/2c/…). Without this reduction, every differentiation step
has to dominate a singularity that moves with the parameter.

## Main result

* `pompeiuKernel_eq_translated_integrand` — the equality above.

## Method

The substitution `η := ζ - z` (equivalently `ζ = η + z`) is
volume-preserving on `ℂ` (Lebesgue is right-invariant under addition).
Apply `MeasureTheory.integral_add_right_eq_self` to the function
`ζ ↦ α ζ · (ζ - z)⁻¹` at shift `z`, then simplify
`(η + z) - z = η`.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-- **Chip 2a — Translation reduction of the Pompeiu kernel.**

By translation invariance of Lebesgue measure on `ℂ`,

  `pompeiuKernel α z = -(π⁻¹) · ∫ η, α (η + z) · η⁻¹`.

The `z`-dependence is now confined to the `α` factor; the singular
factor `η⁻¹` is independent of `z`. This is the standing form used in
all subsequent smoothness arguments (differentiation under the integral
becomes routine once the singularity no longer moves with the
parameter). -/
theorem pompeiuKernel_eq_translated_integrand (α : ℂ → ℂ) (z : ℂ) :
    pompeiuKernel α z = -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z) * η⁻¹ := by
  unfold pompeiuKernel pompeiuIntegrand
  congr 1
  -- Apply translation invariance with shift `z` to the function
  -- `ζ ↦ α ζ * (ζ - z)⁻¹`. Lebesgue on `ℂ` is right-additive-invariant.
  have h_trans :
      (∫ η, (fun ζ : ℂ => α ζ * (ζ - z)⁻¹) (η + z))
        = ∫ ζ, α ζ * (ζ - z)⁻¹ :=
    integral_add_right_eq_self (fun ζ : ℂ => α ζ * (ζ - z)⁻¹) z
  -- Simplify `(η + z) - z = η` in the LHS.
  have h_simp : (fun η : ℂ => (fun ζ : ℂ => α ζ * (ζ - z)⁻¹) (η + z))
      = (fun η : ℂ => α (η + z) * η⁻¹) := by
    funext η
    simp [add_sub_cancel_right]
  rw [h_simp] at h_trans
  exact h_trans.symm

/-! ## Integrability of the translated integrand

The Chip 1c statement transports through the translation: when `α` is
continuous with compact support, the translated integrand
`η ↦ α (η + z) · η⁻¹` is integrable on `ℂ`. This is a direct corollary
of `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport` plus
translation invariance, recorded here as the natural companion to the
kernel translation identity. -/

/-- The translated Pompeiu integrand `η ↦ α (η + z) · η⁻¹` is
integrable when `α` is continuous with compact support. -/
theorem integrable_translated_pompeiuIntegrand_of_continuous_hasCompactSupport
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Integrable (fun η : ℂ => α (η + z) * η⁻¹) volume := by
  -- The translated integrand is the original `pompeiuIntegrand α z`
  -- composed with `η ↦ η + z`. Translation is measure-preserving.
  have h_int := integrable_pompeiuIntegrand_of_continuous_hasCompactSupport
    h_cont h_supp z
  -- We will show pointwise that the translated function `(η ↦ α (η+z) · η⁻¹)`
  -- equals `(pompeiuIntegrand α z) ∘ (· + z)` and use
  -- `MeasurePreserving.integrable_comp_emb` (via `measurePreserving_add_right`).
  have h_mp : MeasurePreserving (fun η : ℂ => η + z) volume volume :=
    measurePreserving_add_right volume z
  have h_emb : MeasurableEmbedding (fun η : ℂ => η + z) :=
    (Homeomorph.addRight z).measurableEmbedding
  have h_comp : (fun η : ℂ => α (η + z) * η⁻¹)
      = (pompeiuIntegrand α z) ∘ (fun η : ℂ => η + z) := by
    funext η
    unfold pompeiuIntegrand
    simp [add_sub_cancel_right]
  rw [h_comp]
  exact (h_mp.integrable_comp_emb h_emb).mpr h_int

end JacobianChallenge.PompeiuKernel

end
