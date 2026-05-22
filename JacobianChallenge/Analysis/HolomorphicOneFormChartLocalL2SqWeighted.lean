/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2Sq
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Weighted chart-local L²-square seminorm

For `om : HolomorphicOneForm X`, `y : X`, and a real-valued weight
`χ : X → ℝ` (typically a partition-of-unity bump centered near `y`),
the weighted chart-local L²-square seminorm is

```
HolomorphicOneForm.chartLocalL2SqWeighted om y χ
  : ℝ≥0∞
  := ∫⁻ z in (chartAt ℂ y).target,
       ENNReal.ofReal (χ ((chartAt ℂ y).symm z))
         * ‖HolomorphicOneForm.localCoeff om y z‖₊^2
       ∂(volume : Measure ℂ)
```

This is chip D₂ of the L²-positivity arc. Once a partition of unity
`{χ_y}_{y : X}` subordinate to the chart-source cover is fixed
(chip D₁), the global Petersson L²-square norm of `om` is the
`∑ᶠ y, chartLocalL2SqWeighted om y χ_y` over a locally finite
support — that assembly is chip D₃ downstream.

This chip ships:
* the definition;
* `chartLocalL2SqWeighted_zero` — zero on the zero form;
* `chartLocalL2SqWeighted_weight_zero` — zero on the zero weight;
* `chartLocalL2SqWeighted_mono_weight` — pointwise-monotone in the
  weight;
* `chartLocalL2SqWeighted_one` — recovers `chartLocalL2Sq` over the
  full chart target when the weight is the constant `1`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory ENNReal NNReal

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Weighted chart-local L²-square seminorm.**

For a holomorphic 1-form `om` on `X`, a chart base point `y : X`, and
a real-valued weight `χ : X → ℝ`, integrate
`(χ ∘ (chartAt ℂ y).symm)(z) * ‖localCoeff om y z‖²` over the chart
target with respect to complex Lebesgue measure. Returns an `ℝ≥0∞`.

The `ENNReal.ofReal` clamps negative `χ`-values to `0`; downstream
chips assume `0 ≤ χ` (e.g. partition-of-unity functions). -/
def chartLocalL2SqWeighted (om : HolomorphicOneForm X) (y : X) (χ : X → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ z in (chartAt ℂ y).target,
    ENNReal.ofReal (χ ((chartAt ℂ y).symm z))
      * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
    ∂(volume : Measure ℂ)

/-- **Weighted seminorm of the zero form is zero**, on every weight. -/
@[simp]
lemma chartLocalL2SqWeighted_zero (y : X) (χ : X → ℝ) :
    chartLocalL2SqWeighted (0 : HolomorphicOneForm X) y χ = 0 := by
  unfold chartLocalL2SqWeighted
  rw [HolomorphicOneForm.localCoeff_zero]
  simp

/-- **Weighted seminorm with zero weight is zero**, for every form. -/
@[simp]
lemma chartLocalL2SqWeighted_weight_zero (om : HolomorphicOneForm X) (y : X) :
    chartLocalL2SqWeighted om y (fun _ => (0 : ℝ)) = 0 := by
  unfold chartLocalL2SqWeighted
  simp

/-- **Monotone in the weight**: if `χ₁ ≤ χ₂` pointwise, the weighted
seminorm is monotone. -/
lemma chartLocalL2SqWeighted_mono_weight (om : HolomorphicOneForm X) (y : X)
    {χ₁ χ₂ : X → ℝ} (h : ∀ x, χ₁ x ≤ χ₂ x) :
    chartLocalL2SqWeighted om y χ₁ ≤ chartLocalL2SqWeighted om y χ₂ := by
  unfold chartLocalL2SqWeighted
  refine lintegral_mono_ae (Filter.Eventually.of_forall fun z => ?_)
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (h _)) _

/-- **Constant-`1` weight recovers the unweighted chart-local L²-square
seminorm** over the full chart target. -/
lemma chartLocalL2SqWeighted_one (om : HolomorphicOneForm X) (y : X) :
    chartLocalL2SqWeighted om y (fun _ => (1 : ℝ))
      = chartLocalL2Sq om y (chartAt ℂ y).target := by
  unfold chartLocalL2SqWeighted chartLocalL2Sq JacobianChallenge.L2NormSq
  simp [ENNReal.ofReal_one]

end HolomorphicOneForm

end
