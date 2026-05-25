/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelRadialWirtinger

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F (Section C, step 1):
radial collapse of the integrand `(∂̄B)(η)/η`

For a radially-symmetric `B(w) = ψ(‖w‖)` on `ℂ` (with `ψ : ℝ → ℝ`
differentiable at `‖η‖` and `η ≠ 0`), the Wirtinger formula
(Chip 3c-F-1) plus the obvious algebraic cancellation `(η/‖η‖)/η =
1/‖η‖` gives the **scalar radial collapse**:

```
(∂̄ B)(η) / η  =  ((ψ'(‖η‖) / (2 ‖η‖)) : ℂ).
```

This is the pointwise identity that — once integrated in polar
coordinates — collapses to the universal constant `-π` for our
specific cutoff (Chip 3c-F-2 main).

## Main result

* `partialZBar_radial_div_eq_radial` — the cancellation above.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric Real
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

open JacobianChallenge

/-- **Radial collapse of the integrand.** For `η ≠ 0` and
`ψ : ℝ → ℝ` differentiable at `‖η‖` with derivative `ψ'`,
```
partialZBar (fun w => (ψ ‖w‖ : ℂ)) η / η = (ψ' / (2 * ‖η‖) : ℝ).
```
The factor `η/‖η‖ : ℂ` from the radial Wirtinger formula cancels
with the dividing `η`, leaving the purely-radial scalar
`(1/(2‖η‖)) · ψ'`. -/
theorem partialZBar_radial_div_eq_radial
    {η : ℂ} (hη : η ≠ 0) {ψ : ℝ → ℝ} {ψ' : ℝ}
    (hψ : HasDerivAt ψ ψ' ‖η‖) :
    partialZBar (fun w : ℂ => ((ψ ‖w‖ : ℝ) : ℂ)) η / η
      = ((ψ' / (2 * ‖η‖) : ℝ) : ℂ) := by
  -- Apply Chip 3c-F-1's radial Wirtinger formula at `z = 0`.
  have h_ne_0 : η ≠ (0 : ℂ) := hη
  -- The Wirtinger formula `partialZBar_radial_of_ne` is stated for
  -- `f(w) = ψ ‖w - z‖`. Specialize with `z := 0`: `‖w - 0‖ = ‖w‖`.
  have h_norm_sub : ∀ w : ℂ, ‖w - (0 : ℂ)‖ = ‖w‖ := fun w => by rw [sub_zero]
  -- Rewrite the function being differentiated.
  have h_fun_eq : (fun w : ℂ => ((ψ ‖w - (0 : ℂ)‖ : ℝ) : ℂ))
      = fun w : ℂ => ((ψ ‖w‖ : ℝ) : ℂ) := by
    funext w; rw [h_norm_sub]
  -- Apply the Wirtinger formula at z = 0.
  have hψ' : HasDerivAt ψ ψ' ‖η - (0 : ℂ)‖ := by rw [h_norm_sub η]; exact hψ
  have h_wirt := partialZBar_radial_of_ne h_ne_0 hψ' (z := (0 : ℂ))
  -- Now `h_wirt : partialZBar (fun w => (ψ ‖w - 0‖ : ℂ)) η = (ψ' / 2) * (η - 0) / ‖η - 0‖`.
  rw [h_fun_eq] at h_wirt
  rw [h_norm_sub η] at h_wirt
  rw [sub_zero] at h_wirt
  -- `h_wirt : partialZBar (fun w => (ψ ‖w‖ : ℂ)) η = ((ψ'/2 : ℝ) : ℂ) * η / ‖η‖`.
  -- Divide by η, cancel.
  rw [h_wirt]
  -- Goal: ((ψ'/2 : ℝ) : ℂ) * η / ‖η‖ / η = ((ψ'/(2·‖η‖) : ℝ) : ℂ).
  have h_norm_ne : ‖η‖ ≠ 0 := norm_ne_zero_iff.mpr h_ne_0
  have h_norm_C_ne : ((‖η‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact h_norm_ne
  -- Goal: ((ψ'/2:ℝ):ℂ) * η / ‖η‖ / η = ((ψ'/(2·‖η‖):ℝ):ℂ).
  -- LHS = ((ψ'/2:ℝ):ℂ) * η / ‖η‖ / η. Rearrange: = ((ψ'/2:ℂ)/‖η‖) * (η/η) = ψ'/(2·‖η‖).
  rw [div_div, div_eq_iff (mul_ne_zero h_norm_C_ne h_ne_0)]
  push_cast
  field_simp

end JacobianChallenge.PompeiuKernel

end
