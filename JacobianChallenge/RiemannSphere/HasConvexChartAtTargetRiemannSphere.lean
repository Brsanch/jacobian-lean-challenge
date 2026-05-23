/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasAdmissibleChartCoverFromConvexChartAtTarget
import JacobianChallenge.Manifold.RiemannSphere

set_option linter.unusedSectionVars false

/-! # `HasConvexChartAtTarget RiemannSphere` instance

For the standard two-chart atlas `{chartN, chartS}` on `RiemannSphere`,
the per-point `chartAt ℂ x` is `chartN` for `x : ℂ` (`coe`) and
`chartS` for `x = ∞`. Both `chartN.target = chartS.target = Set.univ`
(verified in `Manifold/RiemannSphere.lean`), so the per-point target
is `Set.univ` — trivially convex.

This validates the `HasAdmissibleChartCover` instance chain end-to-end
on `RiemannSphere`: the unconditional 2-input item-14 reduction
([`Item14From2InputsUnderConvexChartAt.lean`](../Topology/Item14From2InputsUnderConvexChartAt.lean))
applies to `RiemannSphere` once the two genuine classical inputs
(`hSP` and `h_bslb`) are supplied.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology
open Set
open scoped OnePoint

namespace JacobianChallenge

/-- **`HasConvexChartAtTarget RiemannSphere`** — the per-point chart
`chartAt ℂ x` is either `chartN` or `chartS`, both with target
`Set.univ` (convex). -/
instance : HasConvexChartAtTarget RiemannSphere := by
  refine ⟨?_⟩
  intro x
  -- `chartAt ℂ x = chartN` for `x : ℂ`, `chartS` for `x = ∞`.
  induction x using OnePoint.rec with
  | infty =>
    show Convex ℝ ((chartAt ℂ (∞ : RiemannSphere)).target)
    rw [show ((chartAt ℂ (∞ : RiemannSphere)).target : Set ℂ)
        = RiemannSphere.chartS.target from rfl,
      RiemannSphere.chartS_target]
    exact convex_univ
  | coe z =>
    show Convex ℝ ((chartAt ℂ ((z : RiemannSphere))).target)
    rw [show ((chartAt ℂ ((z : RiemannSphere))).target : Set ℂ)
        = RiemannSphere.chartN.target from rfl,
      RiemannSphere.chartN_target]
    exact convex_univ

end JacobianChallenge

end
