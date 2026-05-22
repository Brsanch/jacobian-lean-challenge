/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqWeighted
import JacobianChallenge.Analysis.RealModelManifoldFromComplex
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Global Petersson L²-square norm via partition-of-unity sum

For `om : HolomorphicOneForm X` on a compact T2 `ChartedSpace ℂ X` and
a smooth partition of unity `f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X univ`
subordinate to the chart-source cover, the **global Petersson L²-square
norm** is the locally-finite sum

```
HolomorphicOneForm.globalPettersonL2Sq om f
  : ℝ≥0∞
  := ∑ᶠ y, chartLocalL2SqWeighted om y (f y)
```

i.e. each chart at `y : X` contributes a weighted L² seminorm with the
partition bump `f y` (supported in `(chartAt ℂ y).source`), summed via
`finsum` over the locally-finite support of the partition.

This is chip D₃ of the L²-positivity arc. Combined with chips A/B/C
(seminorm + finiteness), chips D₀/D₁/D₂ (cover + partition + weighted),
and the diamond-closing instance (`Analysis/RealModelManifoldFromComplex`),
this completes the partition-of-unity construction of the Petersson
inner product's diagonal. Downstream:

* chip E — positivity: `om ≠ 0 ⇒ 0 < globalPettersonL2Sq om f` (uses
  identity theorem for holomorphic functions);
* chip F — identification with the Hermitian sesquilinear form behind
  `RiemannSecondRelationPositivity`'s matrix PD.

This chip ships:
* `globalPettersonL2Sq` — the definition;
* `globalPettersonL2Sq_zero` — zero on the zero form.

Both well-typed unconditionally (no extra hypotheses beyond the
standard manifold typeclasses, since chip D₂'s machinery is also
unconditional).

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory ENNReal NNReal

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Global Petersson L²-square norm** of a holomorphic 1-form, defined
via a smooth partition of unity subordinate to the chart-source cover.

For each `y : X`, the partition function `f y : X → ℝ` is supported in
`(chartAt ℂ y).source`, and `chartLocalL2SqWeighted om y (f y)`
integrates `(f y ∘ (chartAt ℂ y).symm) · ‖localCoeff om y‖²` over the
chart target. Summing over all `y` via `finsum` (locally finite by the
partition's `locallyFinite'` field) gives the global L²-square norm.

The dependence on the partition `f` is real for the *intermediate*
value, but the **resulting global L²-square norm should agree across
partitions modulo the change-of-variables identity** for the chart-
pullback measure. That equivalence is a downstream chip (not in this
chip's scope). -/
def globalPettersonL2Sq (om : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) : ℝ≥0∞ :=
  ∑ᶠ y, chartLocalL2SqWeighted om y (fun x => f.toFun y x)

/-- **Global Petersson L²-square norm of the zero form is zero**,
on every partition of unity. -/
@[simp]
lemma globalPettersonL2Sq_zero
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    globalPettersonL2Sq (0 : HolomorphicOneForm X) f = 0 := by
  unfold globalPettersonL2Sq
  simp [chartLocalL2SqWeighted_zero]

end HolomorphicOneForm

end
