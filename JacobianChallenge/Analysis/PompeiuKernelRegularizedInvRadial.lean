/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import JacobianChallenge.Analysis.PompeiuKernelRadialBump

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3a: regularized inverse, radial-cutoff version

This file mirrors Chip 3c-C₂'s `regularizedInvSub` but uses
`radialCutoff` (the explicit radially-symmetric cutoff from Chip 3c-F-1)
in place of `pompeiuCutoff` (the abstract-bump cutoff from Chip 3c-C₁).
Used downstream by Chip 3c-F-3's substitution + DCT argument on the
second summand: at the unit scale (`ε = 1`, `z = 0`), the radial
cutoff matches `radialCutoff 0 1`, which is what the Chip 3c-F-2-final
universal-constant calculation `∫ ∂̄(radialBump 0 1)(w)/w dA(w) = -π`
talks about.

```
g_ε(η) := (η - z)⁻¹ * ((radialCutoff z ε η : ℝ) : ℂ).
```

Properties (all sorry- and axiom-free, mirroring 3c-C₂):

* `regularizedInvSubRadial z ε η` — definition.
* `regularizedInvSubRadial_eventuallyEq_zero` — `=ᶠ[𝓝 z] 0`, inherited
  from `radialCutoff_eventuallyEq_zero` (Chip 3c-F-1).
* `regularizedInvSubRadial_contDiff` — `ContDiff ℝ n` globally, via
  case split on `ζ = z` vs `ζ ≠ z`.

This file is a chip-3c-C₂ replay, NOT a paraphrase: it uses the
**radial** cutoff and consequently `radialBump 0 1 = unitRadialBumpC`,
the bump whose universal constant is known from Chip 3c-F-2-final. The
`pompeiuCutoff`-based version cannot be used downstream because we do
not have its universal constant. -/

noncomputable section

open Complex Filter Set Topology Metric
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## Definition of the radial regularized inverse factor -/

/-- The radial-cutoff regularized `(η - z)⁻¹` factor:
```
g_ε(η) := (η - z)⁻¹ * (radialCutoff z ε η : ℂ).
```
The cutoff kills the `1/(η - z)` singularity at `η = z`, making the
product `C^∞` everywhere on `ℂ`. -/
def regularizedInvSubRadial (z : ℂ) (ε : ℝ) : ℂ → ℂ :=
  fun η => (η - z)⁻¹ * ((radialCutoff z ε η : ℝ) : ℂ)

/-! ## Local behavior near `z` -/

/-- `regularizedInvSubRadial z ε` is eventually `0` on a neighborhood of
`z`, inheriting from `radialCutoff_eventuallyEq_zero` (Chip 3c-F-1). -/
lemma regularizedInvSubRadial_eventuallyEq_zero (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    regularizedInvSubRadial z ε =ᶠ[𝓝 z] 0 := by
  have h_cutoff := radialCutoff_eventuallyEq_zero z hε
  filter_upwards [h_cutoff] with η h_η
  show (η - z)⁻¹ * ((radialCutoff z ε η : ℝ) : ℂ) = (0 : ℂ → ℂ) η
  have h_η' : radialCutoff z ε η = 0 := h_η
  rw [h_η']
  simp

/-! ## Smoothness off `z` -/

/-- The complex `ofReal` cast is `C^∞` everywhere. (Local copy to keep
the file self-contained; identical to Chip 3c-C₂'s `contDiff_ofReal`.) -/
lemma contDiff_ofReal_radial {n : ℕ∞} : ContDiff ℝ n ((↑) : ℝ → ℂ) :=
  Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)

set_option backward.isDefEq.respectTransparency false in
/-- `(η - z)⁻¹` is `ContDiffAt ℝ n` at any `ζ ≠ z`. (Identical to
Chip 3c-C₂'s `contDiffAt_inv_sub_const`; the
`set_option backward.isDefEq.respectTransparency false in` dodges the
`IsScalarTower ℝ ℂ ℂ` synthesis diamond.) -/
lemma contDiffAt_inv_sub_const_radial (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) {n : ℕ∞} :
    ContDiffAt ℝ n (fun η : ℂ => (η - z)⁻¹) ζ := by
  have h_sub : ContDiffAt ℝ n (fun η : ℂ => η - z) ζ :=
    (contDiff_id.sub contDiff_const).contDiffAt
  have h_ne : (fun η : ℂ => η - z) ζ ≠ 0 := sub_ne_zero.mpr hζ
  exact (contDiffAt_inv (𝕜 := ℂ) h_ne).restrict_scalars ℝ |>.comp ζ h_sub

/-- `regularizedInvSubRadial z ε` is `ContDiffAt ℝ n` at any `ζ ≠ z` —
the product of two `C^∞` factors. -/
lemma regularizedInvSubRadial_contDiffAt_of_ne (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {ζ : ℂ} (hζ : ζ ≠ z) {n : ℕ∞} :
    ContDiffAt ℝ n (regularizedInvSubRadial z ε) ζ := by
  have h_inv : ContDiffAt ℝ n (fun η : ℂ => (η - z)⁻¹) ζ :=
    contDiffAt_inv_sub_const_radial z hζ
  have h_cutoff_real : ContDiffAt ℝ n (radialCutoff z ε) ζ :=
    (radialCutoff_contDiff z hε).contDiffAt
  have h_cutoff_complex :
      ContDiffAt ℝ n (fun η : ℂ => ((radialCutoff z ε η : ℝ) : ℂ)) ζ :=
    contDiff_ofReal_radial.contDiffAt.comp ζ h_cutoff_real
  exact h_inv.mul h_cutoff_complex

/-! ## Smoothness at `z` -/

/-- `regularizedInvSubRadial z ε` is `ContDiffAt ℝ n` at `z` itself: it
is eventually equal to the constant function `0`, which is `C^∞`. -/
lemma regularizedInvSubRadial_contDiffAt_of_eq (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞} :
    ContDiffAt ℝ n (regularizedInvSubRadial z ε) z := by
  have h_const : ContDiffAt ℝ n (fun _ : ℂ => (0 : ℂ)) z := contDiffAt_const
  exact h_const.congr_of_eventuallyEq
    (regularizedInvSubRadial_eventuallyEq_zero z hε)

/-! ## Global smoothness -/

/-- **Chip 3c-F-3a — smoothness of the radial regularized inverse.**
`regularizedInvSubRadial z ε : ℂ → ℂ` is `C^∞`. -/
theorem regularizedInvSubRadial_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (regularizedInvSubRadial z ε) := by
  rw [contDiff_iff_contDiffAt]
  intro ζ
  by_cases hζ : ζ = z
  · subst hζ; exact regularizedInvSubRadial_contDiffAt_of_eq ζ hε
  · exact regularizedInvSubRadial_contDiffAt_of_ne z hε hζ

end JacobianChallenge.PompeiuKernel
