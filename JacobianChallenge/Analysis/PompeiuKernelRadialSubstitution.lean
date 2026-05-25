/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import JacobianChallenge.Analysis.PompeiuKernelSecondSummandIdentity
import JacobianChallenge.Analysis.PompeiuKernelRadialRescaling

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3d-2c: substitution identity for the integral

Under the change of variable `η = z + ε·w`, the second-summand integral

```
∫ ζ : ℂ, α(ζ) · partialZBar (regularizedInvSubRadial z ε) ζ
```

transforms into the unit-scale integral

```
-∫ w : ℂ, α(z + ε·w) · (partialZBar (unitRadialBumpC) w / w).
```

This is the core algebraic identity that takes the second-summand DCT
limit (Chip 3c-F-3d-3) from `ε → 0⁺` for the regularized integral to the
unit-scale integral whose value `-π` is known from Chip 3c-F-2-final.

Proof structure:

* **Pointwise substitution** (`partialZBar_regInvSubRadial_at_rescaled`):
  `∂̄(regularizedInvSubRadial z ε)(z + ε·w) = -ε⁻² · (∂̄(unitRadialBumpC)(w) / w)`.
  Combines Chip 3c-F-3d-1 (`∂̄(regInvSubRadial) = (·-z)⁻¹ · ∂̄(cutoffℂ)`)
  with `∂̄(radialCutoffComplex) = -∂̄(radialBumpComplex)` (linearity of `∂̄`
  on `1 - f`) and Chip 3c-F-3d-2b (rescaling identity on the bump).

* **Translation step**: `∫ ζ, f(ζ) = ∫ η, f(z + η)` via mathlib's
  `integral_add_left_eq_self` for the left-invariant Haar measure on ℂ.

* **Scaling step**: `∫ η, g(η) = ε² · ∫ w, g(ε·w)` via mathlib's
  `Measure.integral_comp_smul` for the additive Haar measure on ℂ with
  `Module.finrank ℝ ℂ = 2`.

All sorry- and axiom-free. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## `∂̄ (radialCutoffComplex z ε) = -∂̄ (radialBumpComplex z ε)` -/

/-- `radialCutoffComplex z ε` is `C¹`. (Cast of the radial cutoff to `ℂ`.) -/
lemma radialCutoffComplex_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (1 : ℕ∞) (radialCutoffComplex z ε) := by
  have h_real : ContDiff ℝ (1 : ℕ∞) (radialCutoff z ε) := radialCutoff_contDiff z hε
  exact Complex.ofRealCLM.contDiff.comp h_real

/-- The `ℂ`-valued radial bump `fun η => ((radialBump z ε η : ℝ) : ℂ)` is `C¹`. -/
lemma radialBumpComplex_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (1 : ℕ∞) (fun η : ℂ => ((radialBump z ε η : ℝ) : ℂ)) := by
  have h_real : ContDiff ℝ (1 : ℕ∞) (radialBump z ε) := radialBump_contDiff z hε
  exact Complex.ofRealCLM.contDiff.comp h_real

/-- `∂̄(radialCutoffComplex z ε) = -∂̄(radialBumpComplex z ε)` pointwise.
Direct from `radialCutoff = 1 - radialBump`, linearity of `∂̄` on `f - g`,
and `∂̄(const) = 0`. -/
lemma partialZBar_radialCutoffComplex_eq_neg
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (η : ℂ) :
    partialZBar (radialCutoffComplex z ε) η
      = -partialZBar (fun w : ℂ => ((radialBump z ε w : ℝ) : ℂ)) η := by
  set h : ℂ → ℂ := fun w => ((radialBump z ε w : ℝ) : ℂ) with h_def
  have h_smooth : ContDiff ℝ (1 : ℕ∞) h := radialBumpComplex_contDiff z hε
  have h_diff_at : DifferentiableAt ℝ h η :=
    (h_smooth.differentiable (by norm_num)).differentiableAt
  have h_one_diff : DifferentiableAt ℝ (fun _ : ℂ => (1 : ℂ)) η :=
    differentiableAt_const _
  have h_eq : radialCutoffComplex z ε = (fun w : ℂ => (1 : ℂ)) - h := by
    funext w
    show ((radialCutoff z ε w : ℝ) : ℂ) = (1 : ℂ) - ((radialBump z ε w : ℝ) : ℂ)
    unfold radialCutoff
    push_cast
    ring
  rw [h_eq]
  rw [partialZBar_sub h_one_diff h_diff_at, partialZBar_const]
  ring

/-! ## Pointwise substitution identity -/

/-- **Pointwise rescaling at the substituted point.** For `ε > 0` and any `w : ℂ`,
```
partialZBar (regularizedInvSubRadial z ε) (z + ε·w)
  = -((ε : ℂ)^2)⁻¹ * (partialZBar unitRadialBumpC w / w).
```
At `w = 0` both sides are zero (the bump is locally constant `1` at the
origin, so `∂̄(unitRadialBumpC) 0 = 0`; the convention `0⁻¹ = 0` in ℂ
makes `(ε·0)⁻¹ = 0` carry through cleanly). At `w ≠ 0`, this is the
direct algebraic combination of Chips 3c-F-3d-1, 3c-F-3d-2b, and the
linearity step above. -/
lemma partialZBar_regInvSubRadial_at_rescaled
    {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    partialZBar (regularizedInvSubRadial z ε) (z + (ε : ℂ) * w)
      = -(((ε : ℂ)^2)⁻¹) * (partialZBar unitRadialBumpC w / w) := by
  -- Step 1: ∂̄(regInvSubRadial)(η) = (η - z)⁻¹ * ∂̄(radialCutoffComplex)(η).
  rw [partialZBar_regInvSubRadial z hε (z + (ε : ℂ) * w)]
  -- Step 2: ∂̄(radialCutoffComplex) = -∂̄(radialBumpComplex).
  rw [partialZBar_radialCutoffComplex_eq_neg z hε (z + (ε : ℂ) * w)]
  -- Step 3: rescaling identity (Chip 3c-F-3d-2b).
  rw [partialZBar_radialBumpComplex_rescaled hε w]
  -- Step 4: rewrite `(z + ε·w) - z = ε·w`.
  have h_sub : z + (ε : ℂ) * w - z = (ε : ℂ) * w := by ring
  rw [h_sub]
  -- Step 5: pure algebra. `((ε:ℂ) * w)⁻¹ * (-(ε⁻¹ * X)) = -(ε²)⁻¹ * (X / w)`.
  -- Uses `mul_inv` valid in a CommGroupWithZero (so `(a · b)⁻¹ = a⁻¹ · b⁻¹`
  -- for ALL a, b including 0).
  rw [mul_inv]
  rw [show ((ε : ℂ))^2 = (ε : ℂ) * (ε : ℂ) from sq (ε : ℂ)]
  rw [mul_inv]
  rw [div_eq_mul_inv]
  ring

/-! ## Integral substitution -/

/-- Helper: `(ε : ℝ) • w = (ε : ℂ) * w` for `w : ℂ`. (Just `Complex.real_smul`,
named for in-line rewriting in the main proof.) -/
private lemma real_smul_complex (ε : ℝ) (w : ℂ) :
    ((ε : ℝ) • w : ℂ) = (ε : ℂ) * w := Complex.real_smul

/-- **Chip 3c-F-3d-2c — substitution identity for the integral.**

```
∫ ζ : ℂ, α(ζ) · partialZBar (regularizedInvSubRadial z ε) ζ
  = -∫ w : ℂ, α(z + ε·w) · (partialZBar unitRadialBumpC w / w).
```

Proof: translate `ζ = z + η` via left-invariance of Lebesgue measure on
ℂ, then rescale `η = ε·w` via `Measure.integral_comp_smul`
(Jacobian factor `|ε^(finrank ℝ ℂ)| = ε²` cancels the `-ε⁻²` from
`partialZBar_regInvSubRadial_at_rescaled`). No integrability hypothesis
needed: the change-of-variable identities are unconditional, and the
final `-1` cancellation is exact in ℂ. -/
theorem integral_alpha_mul_partialZBar_regInvSubRadial_eq_substituted
    (α : ℂ → ℂ) {z : ℂ} {ε : ℝ} (hε : 0 < ε) :
    (∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
      = -∫ w : ℂ, α (z + (ε : ℂ) * w) *
          (partialZBar unitRadialBumpC w / w) := by
  -- Step 1: translation ζ = z + η.
  have h_trans :
      (∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
        = ∫ η : ℂ, α (z + η) * partialZBar (regularizedInvSubRadial z ε) (z + η) := by
    have h := integral_add_left_eq_self
      (μ := (volume : Measure ℂ))
      (f := fun ζ : ℂ => α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
      z
    exact h.symm
  rw [h_trans]
  -- Define J := target RHS (without the leading minus sign).
  set J : ℂ := ∫ w : ℂ, α (z + (ε : ℂ) * w) *
                  (partialZBar unitRadialBumpC w / w) with J_def
  -- Pointwise rewrite at the rescaled point:
  -- α(z + (ε • w)) · ∂̄(...)(z + (ε • w)) = -((ε : ℂ)²)⁻¹ · α(z + ε·w) · (∂̄ / w).
  have h_pointwise : ∀ w : ℂ,
      α (z + ((ε : ℝ) • w : ℂ)) *
        partialZBar (regularizedInvSubRadial z ε) (z + ((ε : ℝ) • w : ℂ))
          = -(((ε : ℂ) ^ 2)⁻¹) *
              (α (z + (ε : ℂ) * w) * (partialZBar unitRadialBumpC w / w)) := by
    intro w
    rw [real_smul_complex ε w]
    rw [partialZBar_regInvSubRadial_at_rescaled hε]
    ring
  -- The translated integral computed via change of variable η = ε • w.
  have hε_sq_ne : ((ε : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hε)
  have hε_C_sq_ne : ((ε : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hε))
  -- `integral_comp_smul` applied to the integrand
  --   F(η) := α(z + η) · ∂̄(regInvSubRadial z ε)(z + η).
  have h_comp :=
    MeasureTheory.Measure.integral_comp_smul
      (μ := (volume : Measure ℂ)) (E := ℂ) (F := ℂ)
      (fun η : ℂ => α (z + η) *
                    partialZBar (regularizedInvSubRadial z ε) (z + η)) ε
  -- Simplify: |((ε^finrank))⁻¹| = (ε^2)⁻¹ (positive base).
  rw [Complex.finrank_real_complex] at h_comp
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ε))] at h_comp
  -- Apply pointwise on RHS of h_comp under the integral sign.
  have h_comp' :
      (∫ w : ℂ, α (z + ((ε : ℝ) • w : ℂ)) *
          partialZBar (regularizedInvSubRadial z ε) (z + ((ε : ℝ) • w : ℂ)))
        = -(((ε : ℂ) ^ 2)⁻¹) * J := by
    have h_eq_integrand :
        (∫ w : ℂ, α (z + ((ε : ℝ) • w : ℂ)) *
            partialZBar (regularizedInvSubRadial z ε) (z + ((ε : ℝ) • w : ℂ)))
          = ∫ w : ℂ, -(((ε : ℂ) ^ 2)⁻¹) *
              (α (z + (ε : ℂ) * w) * (partialZBar unitRadialBumpC w / w)) := by
      apply integral_congr_ae
      filter_upwards with w
      exact h_pointwise w
    rw [h_eq_integrand]
    exact integral_const_mul (-(((ε : ℂ) ^ 2)⁻¹))
      (fun w : ℂ => α (z + (ε : ℂ) * w) * (partialZBar unitRadialBumpC w / w))
  -- Chain: ∫ η, F(η) = ε^2 • ((ε^2)⁻¹ • ∫ x, F(x)) = ε^2 • ∫ x, F(ε•x) = ε^2 • (-((ε:ℂ)^2)⁻¹ * J).
  -- h_comp.symm : ((ε:ℝ)^2)⁻¹ • ∫ x, F(x) = ∫ w, F(ε • w).
  -- chain with h_comp' to get ((ε^2)⁻¹ • ∫ x, F(x)) = -((ε:ℂ)^2)⁻¹ * J.
  have h_chain : ((ε : ℝ) ^ 2)⁻¹ • (∫ x : ℂ, α (z + x) *
                  partialZBar (regularizedInvSubRadial z ε) (z + x))
                = -(((ε : ℂ) ^ 2)⁻¹) * J := h_comp.symm.trans h_comp'
  -- Apply ((ε:ℝ)^2) • to both sides.
  have h_smul := congrArg (fun y : ℂ => ((ε : ℝ) ^ 2 : ℝ) • y) h_chain
  -- h_smul : (fun y => ε^2 • y) (((ε^2)⁻¹) • ∫ x, F x) = (fun y => ε^2 • y) (-((ε:ℂ)^2)⁻¹ * J).
  simp only at h_smul  -- beta-reduce
  rw [show ∀ (a₁ a₂ : ℝ) (b : ℂ), a₁ • a₂ • b = (a₁ * a₂) • b from
      fun a₁ a₂ b => smul_smul a₁ a₂ b,
    mul_inv_cancel₀ hε_sq_ne,
    show ∀ (b : ℂ), (1 : ℝ) • b = b from fun b => one_smul ℝ b] at h_smul
  -- h_smul : ∫ x, F(x) = ((ε:ℝ)^2) • (-((ε:ℂ)^2)⁻¹ * J).
  rw [h_smul]
  -- Final algebra: ε² • (-((ε:ℂ)²)⁻¹ * J) = -J.
  rw [Complex.real_smul]
  have h_cast : ((ε ^ 2 : ℝ) : ℂ) = ((ε : ℂ)) ^ 2 := by push_cast; ring
  have hε_C_ne : ((ε : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
  rw [h_cast]
  field_simp

end JacobianChallenge.PompeiuKernel
