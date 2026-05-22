/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqFinite

/-! # Real-valued chart-local L²-square seminorm

Chip A defined `chartLocalL2Sq om y K : ℝ≥0∞`; chip B showed it is
`< ⊤` on any compact `K ⊆ (chartAt ℂ y).target`. This file packages
the `ENNReal.toReal` projection as the **honest real number**

```
HolomorphicOneForm.chartLocalL2SqReal om y K : ℝ
  := (chartLocalL2Sq om y K).toReal
```

with basic identities. The downstream partition-of-unity sum (chip D)
will operate on these real values, since it needs additivity over
charts (a finite real sum, not an `ℝ≥0∞` lintegral).

Ships:
* `chartLocalL2SqReal_nonneg` — `0 ≤ chartLocalL2SqReal om y K` (always).
* `chartLocalL2SqReal_zero` — zero on the zero form.
* `chartLocalL2SqReal_empty` — zero on the empty set.
* `ofReal_chartLocalL2SqReal_of_isCompact_subset_target` — round-trip
  `ENNReal.ofReal (chartLocalL2SqReal …) = chartLocalL2Sq …` whenever
  `K` is compact and contained in the chart target (uses chip B's
  finiteness).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory ENNReal NNReal

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Real-valued chart-local L²-square seminorm.** -/
def chartLocalL2SqReal (om : HolomorphicOneForm X) (y : X) (K : Set ℂ) : ℝ :=
  (chartLocalL2Sq om y K).toReal

@[simp]
lemma chartLocalL2SqReal_nonneg (om : HolomorphicOneForm X) (y : X)
    (K : Set ℂ) :
    0 ≤ chartLocalL2SqReal om y K :=
  ENNReal.toReal_nonneg

@[simp]
lemma chartLocalL2SqReal_zero (y : X) (K : Set ℂ) :
    chartLocalL2SqReal (0 : HolomorphicOneForm X) y K = 0 := by
  unfold chartLocalL2SqReal
  rw [chartLocalL2Sq_zero]
  rfl

@[simp]
lemma chartLocalL2SqReal_empty (om : HolomorphicOneForm X) (y : X) :
    chartLocalL2SqReal om y (∅ : Set ℂ) = 0 := by
  unfold chartLocalL2SqReal
  rw [chartLocalL2Sq_empty]
  rfl

/-- **`ENNReal.ofReal`-`toReal` round-trip on a compact subset of the
chart target.** Uses chip B's finiteness. -/
lemma ofReal_chartLocalL2SqReal_of_isCompact_subset_target
    (om : HolomorphicOneForm X) (y : X)
    {K : Set ℂ} (hK_compact : IsCompact K)
    (hK_sub : K ⊆ (chartAt ℂ y).target) :
    ENNReal.ofReal (chartLocalL2SqReal om y K) = chartLocalL2Sq om y K := by
  unfold chartLocalL2SqReal
  exact ENNReal.ofReal_toReal
    (chartLocalL2Sq_lt_top_of_isCompact_subset_target om y hK_compact hK_sub).ne

end HolomorphicOneForm

end
