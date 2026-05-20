/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianGenusZeroInstances
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # Typeclass-resolvable form of `JacobianGenusZeroInstances`

`JacobianGenusZeroInstances` ships `compactSpace_Jacobian_holds`,
`chartedSpace_Jacobian_holds`, `isManifold_Jacobian_holds` as `_holds`
theorems taking an explicit `hgenus : genus X = 0` argument and a
`[Subsingleton (Pic0 X)]` instance. On any compact connected complex
1-manifold X with `[Subsingleton (HolomorphicOneForm X)]`, the
`genus X = 0` hypothesis follows from `Module.finrank_zero_of_subsingleton`
+ the unconditional finite-dim instance
`DiskChartCover.holomorphicOneFormFiniteDim_holds`.

This file registers the resulting derivations as **typeclass
instances**, available on any X with the two subsingleton hypotheses:

* `[Subsingleton (HolomorphicOneForm X)]`
* `[Subsingleton (Pic0 X)]`

Both hold unconditionally on `RiemannSphere` (already exploited in
`JacobianRiemannSphereInstances.lean`); on any other X they would
follow from biholomorphism `X ≃ RiemannSphere` (uniformization at
genus 0) + the RS case.

## What this file ships

* `instance instChartedSpace_Jacobian_of_subsingleton_omega` —
  `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` instance under both
  subsingleton hypotheses.
* `instance instIsManifold_Jacobian_of_subsingleton_omega` — analogous.

The existing `compactSpace_Jacobian_holds` already requires only
`[Subsingleton (Pic0 X)]` and is already an instance-eligible theorem;
we re-export it as an instance here for completeness.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`genus X = 0` from `[Subsingleton (HolomorphicOneForm X)]` on a
compact connected complex 1-manifold.** Uses the unconditional finite-
dim instance + `Module.finrank_zero_of_subsingleton`. -/
theorem genus_eq_zero_of_subsingleton_holomorphicOneForm
    [Subsingleton (HolomorphicOneForm X)] :
    JacobianChallenge.genus X = 0 := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X)
  exact Module.finrank_zero_of_subsingleton

/-- **`CompactSpace (Jacobian X)` instance under `[Subsingleton (Pic0 X)]`.**
Re-export of `compactSpace_Jacobian_holds` as an instance. -/
instance instCompactSpace_Jacobian_of_subsingleton_pic0
    [Subsingleton (Pic0 X)] :
    CompactSpace (JacobianChallenge.Jacobian X) :=
  compactSpace_Jacobian_holds

/-- **`ChartedSpace` instance** under both subsingleton hypotheses. -/
noncomputable instance instChartedSpace_Jacobian_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] [Subsingleton (Pic0 X)] :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianChallenge.Jacobian X) :=
  chartedSpace_Jacobian_holds genus_eq_zero_of_subsingleton_holomorphicOneForm

/-- **`IsManifold` instance** under both subsingleton hypotheses. -/
noncomputable instance instIsManifold_Jacobian_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] [Subsingleton (Pic0 X)] :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) _
      instChartedSpace_Jacobian_of_subsingleton_omega :=
  isManifold_Jacobian_holds genus_eq_zero_of_subsingleton_holomorphicOneForm

end JacobianChallenge

end
