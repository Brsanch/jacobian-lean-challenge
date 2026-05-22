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

/-- **Chart-local diagonal is real-valued.** Per-chart-y analog of
`globalPettersonHermitian_diagonal_im`. Follows from Hermitian
symmetry: `H(om, om, y, χ) = conj(H(om, om, y, χ))` ⇒ `im = -im` ⇒
`im = 0`. -/
theorem chartLocalSesquilinear_diagonal_im
    (om : HolomorphicOneForm X) (y : X) (χ : X → ℝ) :
    (chartLocalSesquilinear om om y χ).im = 0 := by
  have h_eq : chartLocalSesquilinear om om y χ
      = (starRingEnd ℂ) (chartLocalSesquilinear om om y χ) :=
    chartLocalSesquilinear_hermitian om om y χ
  have h_im_eq : (chartLocalSesquilinear om om y χ).im
      = ((starRingEnd ℂ) (chartLocalSesquilinear om om y χ)).im := by
    rw [← h_eq]
  rw [Complex.conj_im] at h_im_eq
  linarith

/-- **Chart-local diagonal equals real-cast of real integral.**

For `om om` and any `χ : X → ℝ`, the chart-local Hermitian sesquilinear
form's diagonal equals the real-cast of a *real-valued* Bochner integral:

```
chartLocalSesquilinear om om y χ
  = ↑(∫ z in (chartAt ℂ y).target,
        χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z)
        ∂(volume : Measure ℂ))
```

This is the per-chart identification connecting the ℂ-valued Hermitian
form to a real integral. Useful for downstream positivity reasoning
and for the connection to the L²-square seminorm. -/
theorem chartLocalSesquilinear_diagonal_eq_ofReal
    (om : HolomorphicOneForm X) (y : X) (χ : X → ℝ) :
    chartLocalSesquilinear om om y χ
      = ((∫ z in (chartAt ℂ y).target,
            χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z)
            ∂(volume : Measure ℂ)) : ℂ) := by
  unfold chartLocalSesquilinear
  -- Show pointwise integrand identity.
  have h_pt : ∀ z : ℂ,
      ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
        * (starRingEnd ℂ) (localCoeff om y z))
      = ((χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z) : ℝ) : ℂ) := by
    intro z
    -- localCoeff · conj localCoeff = (normSq localCoeff : ℂ)
    have h_mul_conj : localCoeff om y z * (starRingEnd ℂ) (localCoeff om y z)
        = ((Complex.normSq (localCoeff om y z) : ℝ) : ℂ) := by
      show localCoeff om y z * starRingEnd ℂ (localCoeff om y z)
        = ((Complex.normSq (localCoeff om y z) : ℝ) : ℂ)
      rw [Complex.mul_conj]
    rw [mul_assoc, h_mul_conj]
    push_cast
    ring
  rw [show (fun z : ℂ =>
        (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
          * (starRingEnd ℂ) (localCoeff om y z))
      = (fun z : ℂ =>
        ((χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z) : ℝ) : ℂ))
      from funext h_pt]
  -- After distributing the cast on the RHS via push_cast on both sides,
  -- the equality reduces to rfl (the goal becomes identical on both sides).
  push_cast
  rfl

/-- **Chart-local diagonal nonneg for nonneg weight.**

When `χ ≥ 0` pointwise, the chart-local Hermitian sesquilinear form's
diagonal has nonneg real part. Composes `_diagonal_eq_ofReal` (the
identification with a real-cast integral) with the standard
`integral_nonneg` for nonneg real integrands. -/
theorem chartLocalSesquilinear_diagonal_re_nonneg
    (om : HolomorphicOneForm X) (y : X) {χ : X → ℝ}
    (hχ : ∀ x, 0 ≤ χ x) :
    0 ≤ (chartLocalSesquilinear om om y χ).re := by
  rw [chartLocalSesquilinear_diagonal_eq_ofReal]
  -- Re-bundle the distributed casts back into one outer cast.
  have h_bundle : (∫ z in (chartAt ℂ y).target,
        ((χ ((chartAt ℂ y).symm z) : ℂ) * (Complex.normSq (localCoeff om y z) : ℂ))
        ∂(volume : Measure ℂ))
      = ((∫ z in (chartAt ℂ y).target,
            χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z)
            ∂(volume : Measure ℂ) : ℝ) : ℂ) := by
    -- Step 1: rewrite the integrand into a single ofReal cast.
    have h_pt : ∀ z : ℂ,
        ((χ ((chartAt ℂ y).symm z) : ℂ) * (Complex.normSq (localCoeff om y z) : ℂ))
        = ((χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z) : ℝ) : ℂ) := by
      intro z; push_cast; ring
    rw [show (fun z : ℂ =>
            (χ ((chartAt ℂ y).symm z) : ℂ) * (Complex.normSq (localCoeff om y z) : ℂ))
          = (fun z : ℂ =>
              ((χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z) : ℝ) : ℂ))
          from funext h_pt]
    -- Step 2: apply integral_complex_ofReal.
    exact integral_complex_ofReal
  show 0 ≤ ((∫ z in (chartAt ℂ y).target,
              ((χ ((chartAt ℂ y).symm z) : ℂ) * (Complex.normSq (localCoeff om y z) : ℂ))
              ∂(volume : Measure ℂ))).re
  rw [h_bundle, Complex.ofReal_re]
  refine MeasureTheory.integral_nonneg ?_
  intro z
  exact mul_nonneg (hχ _) (Complex.normSq_nonneg _)

end HolomorphicOneForm

end
