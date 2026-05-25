/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import JacobianChallenge.Analysis.PompeiuKernelRadialIntegrand

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F (Section C, step 2):
universal constant `∫ ζ, (∂̄B)(ζ)/ζ dA = -π`

For the unit-scale radial bump `B(w) := (psiBump 1 ‖w‖ : ℂ)`,

```
∫ ζ : ℂ, partialZBar B ζ / ζ ∂volume = -π.
```

This is the **universal constant** that — after the substitution
`η = z + ε·w` in Chip 3c-F-3 — closes the second-summand DCT limit
`∫ α(η) · ∂̄(regInvSub z hε)(η) → π · α(z)`.

## Proof structure

1. **Pointwise reduction (off `0`)**: by Chip 3c-F-1+2's radial
   collapse `partialZBar_radial_div_eq_radial`, for `ζ ≠ 0`,
   ```
   partialZBar B ζ / ζ = ((deriv (psiBump 1) ‖ζ‖) / (2 · ‖ζ‖) : ℂ).
   ```
2. **Polar coordinates**: `Complex.integral_comp_polarCoord_symm`
   converts `∫ ζ : ℂ, F(ζ) ∂volume` to
   `∫ p in Ioi 0 ×ˢ Ioo (-π) π, p.1 • F(polarCoord.symm p)`. The
   Jacobian factor `p.1` cancels the `1/‖·‖ = 1/p.1` from step 1,
   leaving `((deriv (psiBump 1) p.1 / 2) : ℂ)`.
3. **Fubini**: separate `r` and `θ` integrals.
4. **`θ`-integral**: `∫ θ in Ioo (-π, π), 1 = 2π`.
5. **`r`-integral via FTC**: `psiBump 1` has compact support in
   `[0, 1]`, hence `∫ r in Ioi 0, deriv (psiBump 1) r =
   psiBump 1 1 - psiBump 1 0 = 0 - 1 = -1`.
6. **Combine**: `(2π) · (1/2) · (-1) = -π`.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric Real MeasureTheory
open scoped Real Topology

namespace JacobianChallenge.PompeiuKernel

open JacobianChallenge

/-- The unit-scale radial bump on `ℂ`, lifted to `ℂ → ℂ`. -/
def unitRadialBumpC (w : ℂ) : ℂ := ((radialBump 0 1 w : ℝ) : ℂ)

lemma unitRadialBumpC_eq_psi (w : ℂ) :
    unitRadialBumpC w = ((psiBump 1 ‖w‖ : ℝ) : ℂ) := by
  unfold unitRadialBumpC radialBump
  rw [sub_zero]

/-- `psiBump 1` has support in `[0, 1]`: it equals `0` outside `[0, 1]`. -/
lemma psiBump_one_eq_zero_of_one_le {r : ℝ} (hr : 1 ≤ r) : psiBump 1 r = 0 :=
  psiBump_eq_zero_of_ge one_pos hr

/-- `psiBump 1 0 = 1` (since `0 ≤ 1/2`). -/
lemma psiBump_one_zero : psiBump 1 0 = 1 :=
  psiBump_eq_one_of_le_half one_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- `psiBump 1 1 = 0` (since `1 ≤ 1`). -/
lemma psiBump_one_one : psiBump 1 1 = 0 :=
  psiBump_eq_zero_of_ge one_pos le_rfl

/-- `psiBump 1` is differentiable everywhere. -/
lemma psiBump_one_differentiable : Differentiable ℝ (psiBump 1) :=
  (psiBump_contDiff (ε := 1) one_pos (n := 1)).differentiable (by norm_num)

/-- The derivative of `psiBump 1` is continuous. -/
lemma psiBump_one_deriv_continuous : Continuous (deriv (psiBump 1)) :=
  (psiBump_contDiff (ε := 1) one_pos (n := 2)).continuous_deriv (by norm_num)

/-- For `r ≥ 1`, `psiBump 1` is locally constant `= 0`, so `deriv (psiBump 1) r = 0`. -/
lemma deriv_psiBump_one_eq_zero_of_one_lt {r : ℝ} (hr : 1 < r) :
    deriv (psiBump 1) r = 0 := by
  -- `psiBump 1` is eventually 0 near r (since r > 1, take nbhd avoiding [0, 1]).
  have h_ev : psiBump 1 =ᶠ[𝓝 r] 0 := by
    have h_open : IsOpen (Set.Ioi (1 : ℝ)) := isOpen_Ioi
    have h_mem : Set.Ioi (1 : ℝ) ∈ 𝓝 r := h_open.mem_nhds hr
    filter_upwards [h_mem] with x hx
    exact psiBump_one_eq_zero_of_one_le hx.le
  exact Filter.EventuallyEq.deriv_eq h_ev |>.trans (deriv_const r (0 : ℝ))

/-- For `r < 0`, `psiBump 1 r = smoothTransition (2 - 2r) = 1` (since `2 - 2r > 2 > 1`). -/
lemma psiBump_one_eq_one_of_nonpos {r : ℝ} (hr : r ≤ 0) : psiBump 1 r = 1 := by
  have h_half : r ≤ 1 / 2 := by linarith
  exact psiBump_eq_one_of_le_half one_pos h_half

/-- For `r ≤ 0`, `deriv (psiBump 1) r = 0` (locally constant). Actually for `r < 0`. -/
lemma deriv_psiBump_one_eq_zero_of_neg {r : ℝ} (hr : r < 0) :
    deriv (psiBump 1) r = 0 := by
  have h_ev : psiBump 1 =ᶠ[𝓝 r] 1 := by
    have h_open : IsOpen (Set.Iio (0 : ℝ)) := isOpen_Iio
    have h_mem : Set.Iio (0 : ℝ) ∈ 𝓝 r := h_open.mem_nhds hr
    filter_upwards [h_mem] with x hx
    exact psiBump_one_eq_one_of_nonpos hx.le
  exact Filter.EventuallyEq.deriv_eq h_ev |>.trans (deriv_const r (1 : ℝ))

/-! ## Pointwise identification of the integrand at a polar point -/

/-- For `(r, θ)` with `0 < r`, `polarCoord.symm (r, θ) ≠ 0`. -/
lemma complex_polarCoord_symm_ne_zero {r θ : ℝ} (hr : 0 < r) :
    Complex.polarCoord.symm (r, θ) ≠ 0 := by
  intro h
  have h_norm : ‖Complex.polarCoord.symm (r, θ)‖ = |r| := Complex.norm_polarCoord_symm (r, θ)
  rw [h, norm_zero] at h_norm
  have : |r| = 0 := h_norm.symm
  rw [abs_of_pos hr] at this
  linarith

/-- For `(r, θ)` with `0 < r`, `‖polarCoord.symm (r, θ)‖ = r`. -/
lemma norm_complex_polarCoord_symm_of_pos {r θ : ℝ} (hr : 0 < r) :
    ‖Complex.polarCoord.symm (r, θ)‖ = r := by
  rw [Complex.norm_polarCoord_symm, abs_of_pos hr]

/-- **Polar identification of the integrand.** For `(r, θ)` with `0 < r`,
the integrand `partialZBar (unitRadialBumpC) ζ / ζ` evaluated at
`ζ = polarCoord.symm (r, θ)` equals `((deriv (psiBump 1) r / (2r)) : ℂ)`. -/
lemma integrand_at_polar_symm {r θ : ℝ} (hr : 0 < r) :
    partialZBar unitRadialBumpC (Complex.polarCoord.symm (r, θ))
        / Complex.polarCoord.symm (r, θ)
      = ((deriv (psiBump 1) r / (2 * r) : ℝ) : ℂ) := by
  set ζ := Complex.polarCoord.symm (r, θ)
  have hζ_ne : ζ ≠ 0 := complex_polarCoord_symm_ne_zero hr
  have h_norm_eq : ‖ζ‖ = r := norm_complex_polarCoord_symm_of_pos hr
  -- Apply Chip 3c-F-2's radial collapse.
  -- `unitRadialBumpC w = (psiBump 1 ‖w‖ : ℂ)`.
  have h_fun_eq : unitRadialBumpC = fun w => ((psiBump 1 ‖w‖ : ℝ) : ℂ) := by
    funext w; exact unitRadialBumpC_eq_psi w
  -- HasDerivAt for psiBump 1 at ‖ζ‖.
  have hψ : HasDerivAt (psiBump 1) (deriv (psiBump 1) ‖ζ‖) ‖ζ‖ :=
    (psiBump_one_differentiable.differentiableAt).hasDerivAt
  -- Apply radial collapse.
  have h_collapse :=
    partialZBar_radial_div_eq_radial (η := ζ) hζ_ne (ψ := psiBump 1)
      (ψ' := deriv (psiBump 1) ‖ζ‖) hψ
  rw [h_fun_eq]
  rw [h_collapse, h_norm_eq]

end JacobianChallenge.PompeiuKernel

end
