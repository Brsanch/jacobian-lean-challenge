/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import JacobianChallenge.Analysis.PompeiuKernelRadialIntegral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-2-final: universal constant `-π`

The headline result of Chip 3c-F-2:

```
∫ ζ : ℂ, partialZBar unitRadialBumpC ζ / ζ = -π.
```

Combines Chip 3c-F-2's polar transformation
(`integral_partialZBar_div_eq_polar_integral`) with the explicit `r`/`θ`
evaluations:

* Fubini on `Ioi 0 ×ˢ Ioo (-π) π` via `MeasureTheory.setIntegral_prod_mul`
  applied to the trivial product factorization `f(p.1) = f(p.1) * 1`.
* The `θ`-integral: `∫ θ in Ioo (-π) π, (1 : ℂ) = 2π` via
  `MeasureTheory.setIntegral_const` + `Real.volume_Ioo`.
* FTC on `[0, 1]`: `∫ r in 0..1, deriv (psiBump 1) r = -1` via
  `intervalIntegral.integral_deriv_eq_sub` + `psiBump_one_{zero,one}`.
* Extension to `Ioi 0` via decomposition `Ioi 0 = Ioc 0 1 ∪ Ioi 1` and
  `deriv_psiBump_one_eq_zero_of_one_lt`.
* `ofReal` commutation via `integral_ofReal` (Bochner integration commutes
  with `Complex.ofReal`).
* Combine: `(2π) * (-1/2) = -π`.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric Real MeasureTheory
open scoped Real Topology

namespace JacobianChallenge.PompeiuKernel

open JacobianChallenge

/-! ## FTC for `deriv (psiBump 1)` on `[0, 1]` -/

/-- FTC on `[0, 1]`: `∫ r in 0..1, deriv (psiBump 1) r = -1`. Uses
`intervalIntegral.integral_deriv_eq_sub` with `psiBump 1 1 - psiBump 1 0 = 0 - 1 = -1`. -/
lemma intervalIntegral_deriv_psiBump_one :
    ∫ r in (0 : ℝ)..1, deriv (psiBump 1) r = -1 := by
  have h_diff : ∀ x ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ (psiBump 1) x :=
    fun x _ => psiBump_one_differentiable.differentiableAt
  have h_int : IntervalIntegrable (deriv (psiBump 1)) MeasureTheory.volume 0 1 :=
    psiBump_one_deriv_continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_deriv_eq_sub h_diff h_int,
      psiBump_one_one, psiBump_one_zero]
  norm_num

/-- Set-integral form of FTC on `Ioc 0 1`. -/
lemma setIntegral_Ioc_deriv_psiBump_one :
    ∫ r in Set.Ioc (0 : ℝ) 1, deriv (psiBump 1) r = -1 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact intervalIntegral_deriv_psiBump_one

/-! ## Extension to `Ioi 0` -/

/-- Integrability of `deriv (psiBump 1)` on `Ioc 0 1`: continuous on the
compact `Icc 0 1`, restricted to `Ioc 0 1 ⊆ Icc 0 1`. -/
lemma integrableOn_Ioc_deriv_psiBump_one :
    IntegrableOn (deriv (psiBump 1)) (Set.Ioc (0 : ℝ) 1) :=
  psiBump_one_deriv_continuous.integrableOn_Ioc

/-- `deriv (psiBump 1)` is a.e. zero on `Ioi 1` (every `r > 1` has
`deriv (psiBump 1) r = 0` pointwise). -/
lemma deriv_psiBump_one_ae_zero_Ioi_one :
    (fun r => deriv (psiBump 1) r) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] 0 := by
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
  exact Filter.Eventually.of_forall (fun r hr => deriv_psiBump_one_eq_zero_of_one_lt hr)

/-- Integrability on `Ioi 1`: a.e. equals zero. -/
lemma integrableOn_Ioi_one_deriv_psiBump_one :
    IntegrableOn (deriv (psiBump 1)) (Set.Ioi (1 : ℝ)) := by
  refine (integrable_zero ℝ ℝ (volume.restrict (Set.Ioi (1 : ℝ)))).congr ?_
  exact deriv_psiBump_one_ae_zero_Ioi_one.symm

/-- Integral on `Ioi 1` vanishes. -/
lemma setIntegral_Ioi_one_deriv_psiBump_one :
    ∫ r in Set.Ioi (1 : ℝ), deriv (psiBump 1) r = 0 := by
  rw [MeasureTheory.integral_congr_ae deriv_psiBump_one_ae_zero_Ioi_one]
  simp

/-- `Ioc 0 1` and `Ioi 1` are disjoint. -/
lemma disjoint_Ioc_zero_one_Ioi_one : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, hx⟩ hx'
  exact not_lt.mpr hx hx'

/-- Integrability of `deriv (psiBump 1)` on `Ioi 0`, via decomposition
`Ioi 0 = Ioc 0 1 ∪ Ioi 1`. -/
lemma integrableOn_Ioi_deriv_psiBump_one :
    IntegrableOn (deriv (psiBump 1)) (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact integrableOn_Ioc_deriv_psiBump_one.union integrableOn_Ioi_one_deriv_psiBump_one

/-- **Set-integral on `Ioi 0`**: `∫ r in Ioi 0, deriv (psiBump 1) r = -1`. -/
theorem setIntegral_Ioi_deriv_psiBump_one :
    ∫ r in Set.Ioi (0 : ℝ), deriv (psiBump 1) r = -1 := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.setIntegral_union disjoint_Ioc_zero_one_Ioi_one
        measurableSet_Ioi
        integrableOn_Ioc_deriv_psiBump_one
        integrableOn_Ioi_one_deriv_psiBump_one]
  rw [setIntegral_Ioc_deriv_psiBump_one, setIntegral_Ioi_one_deriv_psiBump_one]
  norm_num

/-! ## ℂ-lifted r-integral -/

/-- The ℂ-lifted r-integral: `∫ r in Ioi 0, ((deriv (psiBump 1) r / 2 : ℝ) : ℂ) = -1/2`. -/
theorem setIntegral_Ioi_ofReal_deriv_psiBump_one_div_two :
    ∫ r in Set.Ioi (0 : ℝ), ((deriv (psiBump 1) r / 2 : ℝ) : ℂ)
      = ((-1 / 2 : ℝ) : ℂ) := by
  -- First compute the real r-integral.
  have h_real : ∫ r in Set.Ioi (0 : ℝ), (deriv (psiBump 1) r / 2 : ℝ) = -1 / 2 := by
    simp_rw [div_eq_mul_inv]
    rw [MeasureTheory.integral_mul_const, setIntegral_Ioi_deriv_psiBump_one]
  -- Lift via ofReal commutation: integral commutes with ℝ → ℂ.
  calc ∫ r in Set.Ioi (0 : ℝ), ((deriv (psiBump 1) r / 2 : ℝ) : ℂ)
      = (((∫ r in Set.Ioi (0 : ℝ), (deriv (psiBump 1) r / 2 : ℝ)) : ℝ) : ℂ) :=
        integral_ofReal
    _ = ((-1 / 2 : ℝ) : ℂ) := by rw [h_real]

/-! ## θ-integral: `∫ θ in Ioo (-π) π, (1 : ℂ) = 2π` -/

/-- The θ-integral of the constant `1 : ℂ` over `Ioo (-π) π` equals `2π`. -/
theorem setIntegral_Ioo_neg_pi_pi_one_complex :
    ∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
  rw [MeasureTheory.setIntegral_const,
      Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg] : -Real.pi ≤ Real.pi)]
  -- Goal: (π - (-π)) • (1 : ℂ) = ↑(2 * π)
  -- `Complex.real_smul : x • z = x * z` (rfl), so `(r : ℝ) • (1 : ℂ)` is defeq to
  -- `((r : ℝ) : ℂ) * 1`. Coerce via `show`.
  show ((Real.pi - (-Real.pi) : ℝ) : ℂ) * 1 = ((2 * Real.pi : ℝ) : ℂ)
  push_cast
  ring

/-! ## Headline: universal constant `-π` -/

/-- **Chip 3c-F-2-final headline**: the universal constant of the
Cauchy-Pompeiu integrand for the unit-scale radial bump is `-π`:

```
∫ ζ : ℂ, partialZBar unitRadialBumpC ζ / ζ = -π.
```

Combines:
- The polar transformation from Chip 3c-F-2 polar
  (`integral_partialZBar_div_eq_polar_integral`): the LHS equals
  `∫ p in Ioi 0 ×ˢ Ioo (-π) π, ((deriv (psiBump 1) p.1 / 2 : ℝ) : ℂ)`.
- Fubini via `setIntegral_prod_mul` after the rewrite
  `f(p.1) = f(p.1) * 1`: factors into
  `(∫ r in Ioi 0, ((deriv (psiBump 1) r / 2 : ℝ) : ℂ))
     * (∫ θ in Ioo (-π) π, (1 : ℂ))`.
- The r-integral equals `(-1/2 : ℂ)` (FTC + ofReal commutation).
- The θ-integral equals `(2π : ℂ)` (constant + Lebesgue measure of `Ioo`).
- `(-1/2) * (2π) = -π`. -/
theorem integral_partialZBar_unitRadialBumpC_div_eq_neg_pi :
    ∫ ζ : ℂ, partialZBar unitRadialBumpC ζ / ζ = ((-Real.pi : ℝ) : ℂ) := by
  rw [integral_partialZBar_div_eq_polar_integral]
  -- Convert the goal's product-space `volume` to the syntactic form
  -- `(volume : Measure ℝ).prod (volume : Measure ℝ)` so that
  -- `setIntegral_prod_mul` (which produces `∂μ.prod ν`) matches.
  -- The two measures are defeq via `volume_eq_prod ℝ ℝ`.
  show ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ((deriv (psiBump 1) p.1 / 2 : ℝ) : ℂ)
         ∂((volume : Measure ℝ).prod (volume : Measure ℝ))
       = ((-Real.pi : ℝ) : ℂ)
  -- Apply Fubini via `setIntegral_prod_mul` with `g ≡ 1`. The product form
  -- `f(p.1) * 1 = f(p.1)` matches our integrand after `simp only [mul_one]`.
  have h_mul := MeasureTheory.setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun r : ℝ => ((deriv (psiBump 1) r / 2 : ℝ) : ℂ))
        (fun _ : ℝ => (1 : ℂ))
        (Set.Ioi (0 : ℝ))
        (Set.Ioo (-Real.pi) Real.pi)
  simp only [mul_one] at h_mul
  -- `rw [h_mul]` runs into a pattern-matching subtlety even though the LHS is
  -- alpha-equivalent. Compose directly via `Eq.trans`.
  refine h_mul.trans ?_
  -- Goal: (∫ x in Ioi 0, ↑(deriv (psiBump 1) x / 2)) * ∫ y in Ioo (-π) π, 1 = ↑(-π)
  -- Pin the bound-variable / elaboration form via `show` then rewrite.
  show (∫ r in Set.Ioi (0 : ℝ), ((deriv (psiBump 1) r / 2 : ℝ) : ℂ))
        * (∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ))
       = ((-Real.pi : ℝ) : ℂ)
  rw [setIntegral_Ioi_ofReal_deriv_psiBump_one_div_two,
      setIntegral_Ioo_neg_pi_pi_one_complex]
  push_cast
  ring

end JacobianChallenge.PompeiuKernel

end
