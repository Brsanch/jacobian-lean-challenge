/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import JacobianChallenge.Manifold.HasFDerivAtRestrictScalarsComplex

set_option linter.unusedSectionVars false

/-! # `DifferentiableOn ℝ (localCoeff om y) (chartAt ℂ y).target`

`HolomorphicOneFormChartCoeffOnTarget.lean` ships
`localCoeff_analyticOn : AnalyticOn ℂ (localCoeff om y) (chartAt ℂ y).target`,
which implies `DifferentiableOn ℂ (localCoeff om y) (chartAt ℂ y).target`.

The hand-rolled `DifferentiableOn.restrictScalarsComplex` from
`HasFDerivAtRestrictScalarsComplex.lean` upgrades this to
`DifferentiableOn ℝ`, bypassing the `IsScalarTower ℝ ℂ ℂ` diamond.

This is the concrete `ℝ`-side differentiability that downstream
`HasFDerivAt`-based interval-integral arguments can consume, even
though the full `ContDiffOn ℝ ∞ (localCoeff om y) ...` upgrade
remains blocked at the `ContDiffOn.restrict_scalars` level.

## What this file ships

* `HolomorphicOneForm.localCoeff_differentiableOn_real` —
  `DifferentiableOn ℝ (localCoeff om y) (chartAt ℂ y).target`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`DifferentiableOn ℝ`-form of `localCoeff_differentiableOn`.**

Derived from `localCoeff_differentiableOn` (ℂ-side) via the hand-rolled
`DifferentiableOn.restrictScalarsComplex` bridge, bypassing the
mathlib `IsScalarTower ℝ ℂ ℂ` diamond. -/
theorem localCoeff_differentiableOn_real
    (om : HolomorphicOneForm X) (y : X) :
    DifferentiableOn ℝ (localCoeff om y) (chartAt ℂ y).target := by
  have h_C : DifferentiableOn ℂ (localCoeff om y) (chartAt ℂ y).target :=
    localCoeff_differentiableOn om y
  exact h_C.restrictScalarsComplex

end HolomorphicOneForm

end
