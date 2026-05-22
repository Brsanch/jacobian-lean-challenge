/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.L2OnManifold
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Chart-local L²-square seminorm of a holomorphic 1-form

For `om : HolomorphicOneForm X`, `y : X`, and `S : Set ℂ` (typically a
subset of `(chartAt ℂ y).target`), this file defines

```
HolomorphicOneForm.chartLocalL2Sq om y S
  : ℝ≥0∞
  := ∫⁻ z in S, ‖HolomorphicOneForm.localCoeff om y z‖₊^2 ∂(volume : Measure ℂ)
```

via `Analysis.L2OnManifold.L2NormSq` against the restricted complex
Lebesgue measure. This is the chart-`y` slice of the Petersson L²-square
norm of `om`; summing the chart-local slices via a partition of unity
gives the global Hodge L²-square norm, and global positivity for
nonzero `om` is the substantive content behind
`RiemannSecondRelationPositivity` at general genus.

This is the **first chip of the L²-positivity arc** for RSRP. It ships
only the measure-theoretic substrate: definition, the trivial `om = 0`
identity, the trivial `S = ∅` identity, and monotonicity in `S`.
Connecting this to the Hermitian form `i · pmatᵀ · J · pmat^*` is the
arc's downstream goal — not in this chip.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory ENNReal NNReal

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Chart-local L²-square seminorm.**

For a holomorphic 1-form `om` on `X`, a base point `y : X`, and a set
`S ⊆ ℂ` (typically `S ⊆ (chartAt ℂ y).target`), the squared L²-norm of
the chart-`y` local coefficient on `S`, as an `ℝ≥0∞`.

Concretely: `∫⁻ z in S, ‖localCoeff om y z‖₊^2 ∂(volume : Measure ℂ)`. -/
def chartLocalL2Sq (om : HolomorphicOneForm X) (y : X) (S : Set ℂ) : ℝ≥0∞ :=
  JacobianChallenge.L2NormSq ((volume : Measure ℂ).restrict S)
    (HolomorphicOneForm.localCoeff om y)

/-- **The chart-local L²-square seminorm of the zero form is zero**
on every set. -/
@[simp]
lemma chartLocalL2Sq_zero (y : X) (S : Set ℂ) :
    chartLocalL2Sq (0 : HolomorphicOneForm X) y S = 0 := by
  unfold chartLocalL2Sq
  rw [HolomorphicOneForm.localCoeff_zero]
  exact JacobianChallenge.L2NormSq_zero _

/-- **Empty-set vanishing.** On `S = ∅`, the chart-local L²-square
seminorm is zero (the restriction is the zero measure). -/
@[simp]
lemma chartLocalL2Sq_empty (om : HolomorphicOneForm X) (y : X) :
    chartLocalL2Sq om y (∅ : Set ℂ) = 0 := by
  unfold chartLocalL2Sq JacobianChallenge.L2NormSq
  simp [Measure.restrict_empty]

/-- **Monotonicity in the set.** If `S ⊆ T`, the chart-local L²-square
seminorm of `om` on `S` is at most that on `T`. -/
lemma chartLocalL2Sq_mono (om : HolomorphicOneForm X) (y : X)
    {S T : Set ℂ} (hST : S ⊆ T) :
    chartLocalL2Sq om y S ≤ chartLocalL2Sq om y T := by
  unfold chartLocalL2Sq JacobianChallenge.L2NormSq
  exact lintegral_mono_set hST

end HolomorphicOneForm

end
