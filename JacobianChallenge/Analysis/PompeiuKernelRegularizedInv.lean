/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic
import JacobianChallenge.Analysis.PompeiuKernelCutoff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-C₂: smoothness of `(η - z)⁻¹ · χ_ε(η)`

This file proves that the **regularized inverse factor**

```
g_ε(η) := (η - z)⁻¹ * ((pompeiuCutoff z hε η : ℝ) : ℂ)
```

is `C^∞` everywhere on `ℂ` (not just off `z`). The trick is the
local-to-global structure of `ContDiff`:

* **Off `z` (η ≠ z)**: `g_ε` is the product of two `C^∞` factors —
  `(·-z)⁻¹` (smooth at η ≠ z, via `hasDerivAt_inv` composed with
  `sub_const`) and the cast `(pompeiuCutoff z hε · : ℝ) → ℂ`
  (smooth everywhere, since `pompeiuCutoff` is `C^∞` and
  `Complex.ofRealCLM` is a continuous linear map).
* **At `z`**: `pompeiuCutoff z hε =ᶠ[𝓝 z] 0` (Chip 3c-C₁'s
  `pompeiuCutoff_eventuallyEq_zero`), so `g_ε =ᶠ[𝓝 z] 0`. Since
  the constant function `0` is `C^∞`,
  `ContDiffAt.congr_of_eventuallyEq` makes `g_ε` `C^∞` at `z` too.

Concatenating gives `ContDiff ℝ n g_ε` for any `n`. This is the
regularized factor used in Chip 3c-C₃'s rectangle-Stokes argument:
the raw factor `(η - z)⁻¹` is not even continuous at `η = z`, but
`g_ε` is globally `C^∞`, so rectangle Stokes applies directly.

## Chip 3 arc context

* Chip 3c-A — pointwise `partialZBar` reduction off `z`.
* Chip 3c-B — `HasFDerivAt` for `α · (·-z)⁻¹` off `z`.
* Chip 3c-C₁ — smooth cutoff `pompeiuCutoff z ε`.
* **Chip 3c-C₂ (this file)** — smoothness of `(η-z)⁻¹ · χ_ε(η)`.
* Chip 3c-C₃ (next) — rectangle Stokes for `α · g_ε`.

## Main results

* `regularizedInvSub z hε : ℂ → ℂ` — the regularized factor.
* `regularizedInvSub_eventuallyEq_zero` — `=ᶠ[𝓝 z] 0`.
* `regularizedInvSub_contDiffAt_of_ne` — `ContDiffAt ℝ n · η` at `η ≠ z`.
* `regularizedInvSub_contDiffAt_of_eq` — `ContDiffAt ℝ n · z`.
* `regularizedInvSub_contDiff` — `ContDiff ℝ n · ` globally.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## Definition of the regularized inverse factor -/

/-- The regularized `(η - z)⁻¹` factor:
```
g_ε(η) := (η - z)⁻¹ * (pompeiuCutoff z hε η : ℂ).
```
The cutoff kills the `1/(η - z)` singularity at `η = z`, making the
product `C^∞` everywhere on `ℂ`. -/
def regularizedInvSub (z : ℂ) {ε : ℝ} (hε : 0 < ε) : ℂ → ℂ :=
  fun η => (η - z)⁻¹ * ((pompeiuCutoff z hε η : ℝ) : ℂ)

/-! ## Local behavior of `regularizedInvSub` -/

/-- `regularizedInvSub z hε` is eventually `0` on a neighborhood of `z`,
inheriting from `pompeiuCutoff_eventuallyEq_zero`. -/
lemma regularizedInvSub_eventuallyEq_zero (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    regularizedInvSub z hε =ᶠ[𝓝 z] 0 := by
  have h_cutoff := pompeiuCutoff_eventuallyEq_zero z hε
  filter_upwards [h_cutoff] with η h_η
  show (η - z)⁻¹ * ((pompeiuCutoff z hε η : ℝ) : ℂ) = (0 : ℂ → ℂ) η
  -- `h_η : pompeiuCutoff z hε η = (0 : ℂ → ℝ) η`, i.e. `= 0`.
  have h_η' : pompeiuCutoff z hε η = 0 := h_η
  rw [h_η']
  simp

/-! ## Smoothness off `z` -/

/-- The complex `ofReal` cast is `C^∞` everywhere. -/
lemma contDiff_ofReal {n : ℕ∞} : ContDiff ℝ n ((↑) : ℝ → ℂ) :=
  Complex.ofRealCLM.contDiff.of_le (mod_cast le_top)

set_option backward.isDefEq.respectTransparency false in
/-- `(η - z)⁻¹` is `ContDiffAt ℝ n` at any `ζ ≠ z`. The
`set_option backward.isDefEq.respectTransparency false in` dodges the
`IsScalarTower ℝ ℂ ℂ` synthesis diamond (same workaround as Chips
3c-A and 3c-B). -/
lemma contDiffAt_inv_sub_const (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) {n : ℕ∞} :
    ContDiffAt ℝ n (fun η : ℂ => (η - z)⁻¹) ζ := by
  have h_sub : ContDiffAt ℝ n (fun η : ℂ => η - z) ζ :=
    (contDiff_id.sub contDiff_const).contDiffAt
  have h_ne : (fun η : ℂ => η - z) ζ ≠ 0 := sub_ne_zero.mpr hζ
  exact (contDiffAt_inv (𝕜 := ℂ) h_ne).restrict_scalars ℝ |>.comp ζ h_sub

/-- `regularizedInvSub z hε` is `ContDiffAt ℝ n` at any `ζ ≠ z` —
the product of two `C^∞` factors. -/
lemma regularizedInvSub_contDiffAt_of_ne (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {ζ : ℂ} (hζ : ζ ≠ z) {n : ℕ∞} :
    ContDiffAt ℝ n (regularizedInvSub z hε) ζ := by
  have h_inv : ContDiffAt ℝ n (fun η : ℂ => (η - z)⁻¹) ζ :=
    contDiffAt_inv_sub_const z hζ
  have h_cutoff_real : ContDiffAt ℝ n (pompeiuCutoff z hε) ζ :=
    (pompeiuCutoff_contDiff z hε).contDiffAt
  have h_cutoff_complex :
      ContDiffAt ℝ n (fun η : ℂ => ((pompeiuCutoff z hε η : ℝ) : ℂ)) ζ :=
    contDiff_ofReal.contDiffAt.comp ζ h_cutoff_real
  exact h_inv.mul h_cutoff_complex

/-! ## Smoothness at `z` -/

/-- `regularizedInvSub z hε` is `ContDiffAt ℝ n` at `z` itself: it is
eventually equal to the constant function `0`, which is `C^∞`. -/
lemma regularizedInvSub_contDiffAt_of_eq (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞} :
    ContDiffAt ℝ n (regularizedInvSub z hε) z := by
  have h_const : ContDiffAt ℝ n (fun _ : ℂ => (0 : ℂ)) z :=
    contDiffAt_const
  exact h_const.congr_of_eventuallyEq
    (regularizedInvSub_eventuallyEq_zero z hε)

/-! ## Global smoothness -/

/-- **Smoothness of `regularizedInvSub` (Chip 3c-C₂).**
`regularizedInvSub z hε : ℂ → ℂ` is `C^∞`. -/
theorem regularizedInvSub_contDiff (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞} :
    ContDiff ℝ n (regularizedInvSub z hε) := by
  rw [contDiff_iff_contDiffAt]
  intro ζ
  by_cases hζ : ζ = z
  · subst hζ; exact regularizedInvSub_contDiffAt_of_eq ζ hε
  · exact regularizedInvSub_contDiffAt_of_ne z hε hζ

end JacobianChallenge.PompeiuKernel
