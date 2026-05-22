/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalSesquilinear
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqWeighted
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Norm

/-! # Bridge: chart-local Hermitian diagonal .re ↔ chart-local L²Sq weighted .toReal

The chart-local strict-positivity for chip S.8 needs identifying the
ℝ-valued `.re` of the ℂ-valued chart-local Hermitian sesquilinear
diagonal with the `ENNReal.toReal` of the chart-local weighted
L²-square seminorm. Once identified, the chart-local strict-positivity
landed in arc E (chip E.3 + supporting infrastructure) lifts to the
ℝ-valued Hermitian side via `ENNReal.toReal_pos` (positivity + finiteness).

For `χ : X → ℝ` with `χ ≥ 0` pointwise AND `χ` continuous, the
chart-local integrand `(χ ∘ chart.symm)(z) * Complex.normSq(localCoeff y z)`
is nonneg, ae-strongly-measurable, and the bridge identity
`integral = (lintegral_of_nonneg).toReal` holds via mathlib's
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae`.

The headline:

```
chartLocalSesquilinear_diagonal_re_eq_chartLocalL2SqWeighted_toReal
    (om : HolomorphicOneForm X) (y : X) {χ : X → ℝ}
    (hχ_nonneg : ∀ x, 0 ≤ χ x) (hχ_cont : Continuous χ) :
    (chartLocalSesquilinear om om y χ).re
      = (chartLocalL2SqWeighted om y χ).toReal
```

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory ENNReal NNReal Complex

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge: chart-local Hermitian diagonal .re equals L²Sq weighted .toReal.**

For `χ ≥ 0` continuous, the real part of the ℂ-valued chart-local
Hermitian sesquilinear diagonal equals the `.toReal` of the ℝ≥0∞-valued
chart-local L²-square weighted seminorm. -/
theorem chartLocalSesquilinear_diagonal_re_eq_chartLocalL2SqWeighted_toReal
    (om : HolomorphicOneForm X) (y : X) {χ : X → ℝ}
    (hχ_nonneg : ∀ x, 0 ≤ χ x) (hχ_cont : Continuous χ) :
    (chartLocalSesquilinear om om y χ).re
      = (chartLocalL2SqWeighted om y χ).toReal := by
  -- Step 1: Unfold chartLocalSesquilinear and rewrite integrand pointwise as
  -- a complex cast of a real value: ↑χ · lc · conj lc = ↑(χ · normSq lc).
  unfold chartLocalSesquilinear
  have h_pt : ∀ z : ℂ,
      ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
        * starRingEnd ℂ (localCoeff om y z))
      = ((χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z) : ℝ) : ℂ) := by
    intro z
    have h_mul_conj : localCoeff om y z * starRingEnd ℂ (localCoeff om y z)
        = ((Complex.normSq (localCoeff om y z) : ℝ) : ℂ) := by
      show localCoeff om y z * starRingEnd ℂ (localCoeff om y z)
        = ((Complex.normSq (localCoeff om y z) : ℝ) : ℂ)
      rw [Complex.mul_conj]
    rw [mul_assoc, h_mul_conj]; push_cast; ring
  rw [show (fun z : ℂ =>
        (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
          * starRingEnd ℂ (localCoeff om y z))
      = (fun z : ℂ =>
        ((χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z) : ℝ) : ℂ))
      from funext h_pt]
  -- Step 2: Pull the ℂ cast out of the integral via integral_complex_ofReal.
  -- ∫ z, ↑(g z) = ↑(∫ z, g z).
  rw [integral_complex_ofReal]
  -- Step 3: .re of an ofReal is the real number.
  rw [Complex.ofReal_re]
  -- Step 4: Now ∫ z in target, χ ∘ symm * normSq lc = (chartLocalL2SqWeighted om y χ).toReal.
  -- Set g := χ ∘ symm * normSq lc, prove nonneg + ae strongly measurable.
  set g : ℂ → ℝ := fun z => χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z)
    with hg_def
  show ∫ z in (chartAt ℂ y).target, g z ∂(volume : Measure ℂ)
      = (chartLocalL2SqWeighted om y χ).toReal
  have hg_nonneg : ∀ z, 0 ≤ g z := by
    intro z
    rw [hg_def]
    exact mul_nonneg (hχ_nonneg _) (Complex.normSq_nonneg _)
  have hg_nonneg_ae : 0 ≤ᵐ[(volume : Measure ℂ).restrict (chartAt ℂ y).target] g :=
    Filter.Eventually.of_forall hg_nonneg
  have h_chart_symm_cont : ContinuousOn (chartAt ℂ y).symm (chartAt ℂ y).target :=
    (chartAt ℂ y).continuousOn_symm
  have h_lc_cont : ContinuousOn (localCoeff om y) (chartAt ℂ y).target :=
    (localCoeff_analyticOn om y).continuousOn
  have h_normSq_cont : Continuous Complex.normSq := Complex.continuous_normSq
  have hg_cont_on : ContinuousOn g (chartAt ℂ y).target := by
    rw [hg_def]
    refine ContinuousOn.mul ?_ ?_
    · exact hχ_cont.comp_continuousOn h_chart_symm_cont
    · exact h_normSq_cont.comp_continuousOn h_lc_cont
  have hg_aestronglyMeas :
      AEStronglyMeasurable g
        ((volume : Measure ℂ).restrict (chartAt ℂ y).target) :=
    hg_cont_on.aestronglyMeasurable (chartAt ℂ y).open_target.measurableSet
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hg_nonneg_ae hg_aestronglyMeas]
  -- Step 5: Identify the lintegral integrand with chartLocalL2SqWeighted's.
  congr 1
  unfold chartLocalL2SqWeighted
  refine MeasureTheory.lintegral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro z
  show ENNReal.ofReal (g z)
      = ENNReal.ofReal (χ ((chartAt ℂ y).symm z)) * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
  rw [hg_def]
  show ENNReal.ofReal (χ ((chartAt ℂ y).symm z) * Complex.normSq (localCoeff om y z))
      = ENNReal.ofReal (χ ((chartAt ℂ y).symm z)) * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
  rw [ENNReal.ofReal_mul (hχ_nonneg _)]
  have h_normSq_eq : Complex.normSq (localCoeff om y z) = ‖localCoeff om y z‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  rw [h_normSq_eq]
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show ENNReal.ofReal ‖localCoeff om y z‖ = (‖localCoeff om y z‖₊ : ℝ≥0∞)
        from (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).trans (by rfl)]

end HolomorphicOneForm

end
