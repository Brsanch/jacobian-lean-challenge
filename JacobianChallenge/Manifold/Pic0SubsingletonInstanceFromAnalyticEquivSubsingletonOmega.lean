/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Pic0SubsingletonFromAnalyticEquivGenusZero
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # `Subsingleton (Pic0 X)` typeclass instance from `[HasPic0AnalyticEquiv X]` + `[Subsingleton ω]`

Registers `Subsingleton (Pic0 X)` as a typeclass instance, automatically
derivable from `[HasPic0AnalyticEquiv X] + [Subsingleton (HolomorphicOneForm X)]`.
Genus 0 follows from Subsingleton ω + DiskChartCover finite-dim.

Combined with `JacobianGenusZeroInstancesAuto`'s two-subsingleton
instances, this discharges items 5/11/12/13 on `Jacobian X` for any X
with those two typeclass instances.

## What ships

* `instance instSubsingleton_pic0_of_hasPic0AnalyticEquiv_subsingleton_omega`
  — Subsingleton (Pic0 X) instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

/-- **`Subsingleton (Pic0 X)` instance** under `[HasPic0AnalyticEquiv X]`
+ `[Subsingleton (HolomorphicOneForm X)]`. -/
instance instSubsingleton_pic0_of_hasPic0AnalyticEquiv_subsingleton_omega
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasPic0AnalyticEquiv X]
    [Subsingleton (HolomorphicOneForm X)] :
    Subsingleton (Pic0 X) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds
  have h_genus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  exact subsingleton_pic0_of_hasPic0AnalyticEquiv_genus_zero h_genus

end JacobianChallenge

end
