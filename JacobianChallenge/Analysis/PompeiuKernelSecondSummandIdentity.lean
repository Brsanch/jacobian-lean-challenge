/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelLeibniz
import JacobianChallenge.Analysis.PompeiuKernelRegularizedInvRadial

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3d-1: ∂̄ of the radial regularized inverse

The pointwise identity that powers the second-summand DCT argument
(Chip 3c-F-3d). For all `η : ℂ`,

```
partialZBar (regularizedInvSubRadial z ε) η
  = (η - z)⁻¹ * partialZBar (fun w => ((radialCutoff z ε w : ℝ) : ℂ)) η.
```

Off `z`: Leibniz on the product `(η - z)⁻¹ · cutoff` combined with
`partialZBar_inv_sub_const_eq_zero` (Chip 3c-A) — the holomorphic
factor's contribution vanishes.

At `η = z`: both sides are `0` because
`regularizedInvSubRadial z ε =ᶠ[𝓝 z] 0` (Chip 3c-F-3a) and the lifted
cutoff is also eventually `0` (from `radialCutoff_eventuallyEq_zero`,
Chip 3c-F-1), so both `partialZBar`s vanish at `z`.

This is the radial-cutoff analog of the algebraic step that drives
Chip 3c-A's Leibniz reduction off `z` — extended here to ALL `η`
(including `z`) by the eventual-vanishing argument.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## The lifted radial cutoff -/

/-- The radial cutoff lifted to a `ℂ`-valued function. -/
def radialCutoffComplex (z : ℂ) (ε : ℝ) : ℂ → ℂ :=
  fun η => ((radialCutoff z ε η : ℝ) : ℂ)

/-- `radialCutoffComplex z ε =ᶠ[𝓝 z] 0`. -/
lemma radialCutoffComplex_eventuallyEq_zero (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    radialCutoffComplex z ε =ᶠ[𝓝 z] 0 := by
  have h := radialCutoff_eventuallyEq_zero z hε
  filter_upwards [h] with η hη
  show ((radialCutoff z ε η : ℝ) : ℂ) = (0 : ℂ → ℂ) η
  have hη' : radialCutoff z ε η = 0 := hη
  rw [hη']
  simp

/-- `partialZBar (radialCutoffComplex z ε) z = 0`: at the cutoff's
center, the lifted cutoff is eventually `0`, so its antiholomorphic
derivative vanishes. -/
lemma partialZBar_radialCutoffComplex_at_z (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    partialZBar (radialCutoffComplex z ε) z = 0 := by
  have h_const : partialZBar (fun _ : ℂ => (0 : ℂ)) z = 0 := by
    unfold partialZBar
    simp
  -- `partialZBar` respects eventually-equal-to-constant.
  have h_eq : radialCutoffComplex z ε =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
    have := radialCutoffComplex_eventuallyEq_zero z hε
    filter_upwards [this] with η hη
    exact hη
  -- `partialZBar` of two functions agreeing eventually is the same.
  unfold partialZBar
  -- `fderiv ℝ f` only depends on local values; congr ae from eventually eq.
  have h_fderiv : fderiv ℝ (radialCutoffComplex z ε) z = fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z :=
    Filter.EventuallyEq.fderiv_eq h_eq
  rw [h_fderiv]
  simp

/-! ## The identity -/

/-- The Leibniz-reduction identity for the radial regularized inverse,
**off `z`**: `partialZBar(regInvSubRadial z ε)(η) = (η-z)⁻¹ · ∂̄(cutoffℂ)(η)`. -/
lemma partialZBar_regInvSubRadial_of_ne
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) {η : ℂ} (hη : η ≠ z) :
    partialZBar (regularizedInvSubRadial z ε) η
      = (η - z)⁻¹ * partialZBar (radialCutoffComplex z ε) η := by
  -- Recast `regularizedInvSubRadial z ε` as the product `(·-z)⁻¹ * cutoffℂ`.
  set f : ℂ → ℂ := fun w => (w - z)⁻¹ with hf_def
  set g : ℂ → ℂ := radialCutoffComplex z ε with hg_def
  -- Pointwise equality.
  have h_eq : regularizedInvSubRadial z ε = f * g := by
    funext w; rfl
  -- f differentiable at η ≠ z.
  have h_f_diff : DifferentiableAt ℝ f η := differentiableAt_real_inv_sub_const z hη
  -- g differentiable everywhere (since ContDiff via radialCutoff_contDiff + ofReal).
  have h_ofReal_contDiff : ContDiff ℝ (1 : ℕ∞) ((↑) : ℝ → ℂ) :=
    Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)
  have h_g_smooth : ContDiff ℝ (1 : ℕ∞) g :=
    h_ofReal_contDiff.comp (radialCutoff_contDiff z hε)
  have h_g_diff : DifferentiableAt ℝ g η :=
    (h_g_smooth.differentiable (by norm_num)).differentiableAt
  -- f has vanishing partialZBar at η ≠ z (it is ℂ-holomorphic).
  have h_f_pzb : partialZBar f η = 0 := partialZBar_inv_sub_const_eq_zero z hη
  -- Apply Leibniz.
  rw [h_eq, partialZBar_mul h_f_diff h_g_diff, h_f_pzb, zero_mul, zero_add]

/-- The Leibniz-reduction identity for the radial regularized inverse,
**at `η = z`**: both sides are `0`. -/
lemma partialZBar_regInvSubRadial_at_z
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    partialZBar (regularizedInvSubRadial z ε) z
      = (z - z)⁻¹ * partialZBar (radialCutoffComplex z ε) z := by
  -- LHS = 0 since regularizedInvSubRadial =ᶠ[𝓝 z] 0.
  have h_lhs : partialZBar (regularizedInvSubRadial z ε) z = 0 := by
    have h_eq : regularizedInvSubRadial z ε =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
      have := regularizedInvSubRadial_eventuallyEq_zero z hε
      filter_upwards [this] with η hη
      exact hη
    unfold partialZBar
    have h_fderiv : fderiv ℝ (regularizedInvSubRadial z ε) z
        = fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z :=
      Filter.EventuallyEq.fderiv_eq h_eq
    rw [h_fderiv]
    simp
  -- RHS = 0: `(z - z)⁻¹ = 0⁻¹ = 0` in ℂ.
  rw [h_lhs]
  simp

/-- **Chip 3c-F-3d-1.** Pointwise identity for the antiholomorphic
derivative of the radial regularized inverse:
```
partialZBar (regularizedInvSubRadial z ε) η
  = (η - z)⁻¹ * partialZBar (radialCutoffComplex z ε) η.
```
Holds for all `η : ℂ` — off `z` by Leibniz + holomorphy of `(·-z)⁻¹`,
at `η = z` by the eventually-zero of both factors and the convention
`(0 : ℂ)⁻¹ = 0`. -/
theorem partialZBar_regInvSubRadial (z : ℂ) {ε : ℝ} (hε : 0 < ε) (η : ℂ) :
    partialZBar (regularizedInvSubRadial z ε) η
      = (η - z)⁻¹ * partialZBar (radialCutoffComplex z ε) η := by
  by_cases hη : η = z
  · rw [hη]
    exact partialZBar_regInvSubRadial_at_z z hε
  · exact partialZBar_regInvSubRadial_of_ne z hε hη

end JacobianChallenge.PompeiuKernel
