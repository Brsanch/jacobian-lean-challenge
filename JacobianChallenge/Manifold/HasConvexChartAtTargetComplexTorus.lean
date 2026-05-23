/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasAdmissibleChartCoverFromConvexChartAtTarget
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeChartedSpace

set_option linter.unusedSectionVars false

/-! # `HasConvexChartAtTarget (ℂ ⧸ L)` instance

For the complex torus `T_L = ℂ ⧸ L`, the `ChartedSpace ℂ (ℂ ⧸ L)`
instance from
[`chartedSpace_quotient_of_zlattice`](PeriodLatticeChartedSpace.lean)
takes `chartAt ℂ q = (localChart L _ q.out).symm`, whose target
equals `(localChart L _ q.out).source = Metric.ball q.out (r/2)` —
an open ball in `ℂ`, hence convex.

This validates the chip-D arc + chart-cover lift + 2-input item-14
reduction end-to-end on the genus-1 case `ℂ ⧸ L`: the
`HasAdmissibleChartCover (ℂ ⧸ L)` instance follows automatically,
discharging both `h_smooth_b` and `h_ftc_b` of the 4-input item-14
formulation for any holomorphic 1-form on `ℂ ⧸ L`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology
open Set Metric

namespace JacobianChallenge

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`HasConvexChartAtTarget (ℂ ⧸ L)`** — the per-point chart-target
is `Metric.ball q.out (discRadius L / 2)`, an open ball in `ℂ`. -/
instance : HasConvexChartAtTarget (ℂ ⧸ L) := by
  refine ⟨?_⟩
  intro q
  -- `chartAt ℂ q = (localChart L _ q.out).symm` from
  -- `chartedSpace_quotient_of_zlattice`.
  show Convex ℝ ((chartAt ℂ q).target)
  -- The target of the symm is the source of the original local chart,
  -- which is `Metric.ball q.out (discRadius L / 2)` by construction.
  have h_target_eq :
      ((chartAt ℂ q).target : Set ℂ)
        = Metric.ball (Quotient.out q) (discRadius L / 2) := by
    -- `chartAt ℂ q = (localChart L _ q.out).symm`, `.symm.target = .source`,
    -- `.source = Metric.ball e (r/2)` by `rfl`.
    show ((localChart L (discRadius_separates L)
            (Quotient.out q)).symm.target : Set ℂ)
      = Metric.ball (Quotient.out q) (discRadius L / 2)
    rw [(localChart L (discRadius_separates L) (Quotient.out q)).symm_target]
    rfl
  rw [h_target_eq]
  exact convex_ball _ _

end JacobianChallenge

end
