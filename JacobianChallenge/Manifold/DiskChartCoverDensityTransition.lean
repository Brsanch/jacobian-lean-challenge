/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityCoverage
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option linter.unusedSectionVars false

/-! # Transition factor primitive for the multi-chart density bound

For two base points `x, y` of a `DiskChartCover` and a point
`q : X` in the chart overlap `(chartAt ℂ x).source ∩ (chartAt ℂ y).source`,
the **transition factor** `transitionFactor x y q : ℂ` is the value of the
tangent-bundle coordinate-change CLM at `q`, applied to the tangent basis
vector `1 : ℂ`. Geometrically, this is the holomorphic derivative of the
chart transition `(chartAt y) ∘ (chartAt x).symm` at the chart-image of
`q`.

This file ships:

* `DiskChartCover.transitionFactor x y q : ℂ` — definition.
* `DiskChartCover.continuousOn_transitionFactor` — `ContinuousOn` on the
  chart overlap, via `VectorBundleCore.continuousOn_coordChange` +
  `ContinuousOn.clm_apply`.

The downstream **identity**
`localCoeff om x p = (transitionFactor x y q) · localCoeff om y ((chartAt y) q)`
(for `p ∈ (chartAt x).target` with `q := (chartAt x).symm p ∈ (chartAt y).source`)
is sketched in the docstring of `transitionFactor` and discharged in the
next chip.

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-! ## The transition factor -/

/-- The (holomorphic) **transition factor** at a point `q : X` from
chart-`x` coordinates to chart-`y` coordinates: the value of
`(tangentBundleCore _ X).coordChange (achart x) (achart y) q` applied to
`1 : ℂ`.

Geometrically: the holomorphic derivative of the chart transition
`(chartAt y) ∘ (chartAt x).symm` at `(chartAt x) q`. Continuous in `q` on
the chart overlap.

For any holomorphic 1-form `om` and `p ∈ (chartAt x).target` with
`q := (chartAt x).symm p ∈ (chartAt y).source`, the per-point
density identity reads

  `localCoeff om x p = transitionFactor x y q · localCoeff om y ((chartAt y) q)`.

This identity is the algebraic core of the multi-chart density bound;
it is discharged in a follow-up chip. -/
def transitionFactor (x y q : X) : ℂ :=
  ((tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ x) (achart ℂ y) q : ℂ →L[ℂ] ℂ) 1

/-- Continuity of `transitionFactor` in `q`, on the chart overlap. -/
theorem continuousOn_transitionFactor (x y : X) :
    ContinuousOn (transitionFactor (X := X) x y)
      ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) := by
  -- `transitionFactor x y q = (coordChange q) 1`. Apply
  -- `ContinuousOn.clm_apply` with `f := fun q => coordChange q`
  -- (continuous on the overlap) and `g := fun _ => 1` (continuous).
  have h_cc : ContinuousOn
      (fun q : X => (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x) (achart ℂ y) q)
      ((tangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ x) ∩
        (tangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y)) :=
    (tangentBundleCore (𝓘(ℂ, ℂ)) X).continuousOn_coordChange
      (achart ℂ x) (achart ℂ y)
  have h_g : ContinuousOn (fun _ : X => (1 : ℂ))
      ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) :=
    continuousOn_const
  -- `baseSet (achart x) = (chartAt x).source` definitionally.
  have h_cc' : ContinuousOn
      (fun q : X => (tangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x) (achart ℂ y) q)
      ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) := h_cc
  exact h_cc'.clm_apply h_g

end DiskChartCover

end JacobianChallenge

end
