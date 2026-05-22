/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # ℂ-valued chart-local sesquilinear pairing for holomorphic 1-forms

This is chip **S.1** of arc S (surface-integration assembly to close
RFBR + RSRP). It extends chip D₂'s `ℝ≥0∞`-valued weighted L²-square
seminorm to a ℂ-valued Hermitian sesquilinear pairing.

For `om, eta : HolomorphicOneForm X`, `y : X`, and a real-valued weight
`χ : X → ℝ`, define

```
HolomorphicOneForm.chartLocalSesquilinear om eta y χ : ℂ
  := ∫ z in (chartAt ℂ y).target,
       ((χ ((chartAt ℂ y).symm z) : ℂ)
         * localCoeff om y z * conj (localCoeff eta y z))
       ∂(volume : Measure ℂ)
```

(Bochner integral, ℂ-valued.) The diagonal `om = eta` recovers the
real-valued weighted L²-square seminorm of chip D₂ up to a coercion;
the off-diagonal pairing is the substantive content that connects to
the period-matrix Hermitian form `i Πᵀ J Π̄` via the bridge identity
(downstream chips).

This chip ships only the basic API:
* `chartLocalSesquilinear` — definition.
* `chartLocalSesquilinear_zero_left` — zero on the zero `om`.
* `chartLocalSesquilinear_zero_right` — zero on the zero `eta`.
* `chartLocalSesquilinear_hermitian` — Hermitian symmetry
  `chartLocalSesquilinear om eta y χ = conj (chartLocalSesquilinear eta om y χ)`.

ℂ-linearity in `om` and conj-linearity in `eta` follow from `localCoeff`'s
linearity properties (already in tree) + `integral_add` / `integral_smul`;
those API expansions are deferred to a follow-up chip.

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff ComplexConjugate
open MeasureTheory ENNReal NNReal Complex

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **ℂ-valued chart-local sesquilinear pairing.**

The chart-`y` Bochner integral of
`(χ ∘ chart.symm)(z) · localCoeff om y z · conj (localCoeff eta y z)`
over the chart target, with respect to the complex Lebesgue measure.

Diagonal `om = eta`: this is real-valued and equals the chip D₂
`chartLocalL2SqWeighted` cast to `ℝ → ℂ` (up to ENNReal/ℝ conversion).
Off-diagonal: the Hermitian sesquilinear content that connects to
period-matrix forms. -/
def chartLocalSesquilinear (om eta : HolomorphicOneForm X) (y : X)
    (χ : X → ℝ) : ℂ :=
  ∫ z in (chartAt ℂ y).target,
    ((χ ((chartAt ℂ y).symm z) : ℂ)
      * localCoeff om y z * (starRingEnd ℂ) (localCoeff eta y z))
    ∂(volume : Measure ℂ)

/-- **Zero on the zero left argument.** -/
@[simp]
lemma chartLocalSesquilinear_zero_left (eta : HolomorphicOneForm X) (y : X)
    (χ : X → ℝ) :
    chartLocalSesquilinear (0 : HolomorphicOneForm X) eta y χ = 0 := by
  unfold chartLocalSesquilinear
  rw [HolomorphicOneForm.localCoeff_zero]
  simp

/-- **Zero on the zero right argument.** -/
@[simp]
lemma chartLocalSesquilinear_zero_right (om : HolomorphicOneForm X) (y : X)
    (χ : X → ℝ) :
    chartLocalSesquilinear om (0 : HolomorphicOneForm X) y χ = 0 := by
  unfold chartLocalSesquilinear
  rw [HolomorphicOneForm.localCoeff_zero]
  simp

/-- **Hermitian symmetry**: swapping arguments conjugates the value. -/
theorem chartLocalSesquilinear_hermitian
    (om eta : HolomorphicOneForm X) (y : X) (χ : X → ℝ) :
    chartLocalSesquilinear om eta y χ
      = (starRingEnd ℂ) (chartLocalSesquilinear eta om y χ) := by
  unfold chartLocalSesquilinear
  -- Strategy: rewrite the LHS integrand as conj of the RHS integrand,
  -- then apply integral_conj.
  -- Step 1: pointwise integrand identity.
  have h_pt : ∀ z : ℂ,
      ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
        * (starRingEnd ℂ) (localCoeff eta y z))
      = (starRingEnd ℂ)
          ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff eta y z
            * (starRingEnd ℂ) (localCoeff om y z)) := by
    intro z
    have h_real_conj : (starRingEnd ℂ) ((χ ((chartAt ℂ y).symm z) : ℂ))
        = (χ ((chartAt ℂ y).symm z) : ℂ) := Complex.conj_ofReal _
    simp only [map_mul, starRingEnd_apply, star_star]
    rw [show star ((χ ((chartAt ℂ y).symm z) : ℝ) : ℂ)
          = ((χ ((chartAt ℂ y).symm z) : ℝ) : ℂ) from h_real_conj]
    ring
  -- Step 2: rewrite the LHS using h_pt.
  rw [show (fun z : ℂ => (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
              * (starRingEnd ℂ) (localCoeff eta y z))
        = (fun z : ℂ => (starRingEnd ℂ)
              ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff eta y z
                * (starRingEnd ℂ) (localCoeff om y z))) from funext h_pt]
  -- Step 3: integral_conj on the resulting form (setIntegral = integral against restricted measure).
  exact integral_conj

end HolomorphicOneForm

end
