/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquivSubsingletonOmegaRS
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim
import JacobianChallenge.Divisor.Pic0HolomorphicEquivSubsingleton
import JacobianChallenge.Topology.UniformizationGenus0Hypothesis

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasPic0AnalyticEquiv X` from a biholomorphism `X ≃ω RS`, UNCONDITIONAL

The closing chip on top of
`hasPic0AnalyticEquiv_of_holomorphicEquiv_RS_subsingleton_pic0`: the
auxiliary `[Subsingleton (Pic0 X)]` hypothesis is automatic from the
biholomorphism + `Subsingleton (Pic0 RiemannSphere)` (unconditional in
tree via `Pic0RiemannSphereSubsingleton.lean`), composed through the
just-shipped `subsingleton_pic0_of_holomorphicEquiv` from
`Divisor/Pic0HolomorphicEquivSubsingleton.lean`.

## What ships

* `hasPic0AnalyticEquiv_of_holomorphicEquiv_RS` — HJAE X from any
  biholomorphism `X ≃ω RS`, unconditional.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJAE X from a biholomorphism `X ≃ω RS`, unconditional.** -/
theorem hasPic0AnalyticEquiv_of_holomorphicEquiv_RS
    (φ : HolomorphicEquiv X RiemannSphere) :
    HasPic0AnalyticEquiv X := by
  haveI : Subsingleton (Pic0 RiemannSphere) := subsingleton_pic0_RiemannSphere
  haveI : Subsingleton (Pic0 X) := subsingleton_pic0_of_holomorphicEquiv φ
  exact hasPic0AnalyticEquiv_of_holomorphicEquiv_RS_subsingleton_pic0 φ

/-- **HJAE X from `UniformizationGenus0Hypothesis X + genus = 0`,
unconditional.** Composes uniformization (genus 0 ⟹ biholomorphic to
RS) with the unconditional biholomorphism chip above. -/
theorem hasPic0AnalyticEquiv_of_uniformizationGenus0_genus_zero
    [UniformizationGenus0Hypothesis X]
    (h_genus : JacobianChallenge.genus X = 0) :
    HasPic0AnalyticEquiv X := by
  obtain ⟨φ⟩ := UniformizationGenus0Hypothesis.out (X := X) h_genus
  exact hasPic0AnalyticEquiv_of_holomorphicEquiv_RS φ

/-- **HJAE X from `UniformizationGenus0Hypothesis X + Subsingleton ω`,
unconditional.** Subsingleton ω ⟹ genus = 0 via the unconditional
`DiskChartCover.holomorphicOneFormFiniteDim_holds`. -/
theorem hasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega
    [UniformizationGenus0Hypothesis X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasPic0AnalyticEquiv X := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds
  have h_genus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  exact hasPic0AnalyticEquiv_of_uniformizationGenus0_genus_zero h_genus

/-- **Typeclass instance form**: `HasPic0AnalyticEquiv X` automatic
under `[UniformizationGenus0Hypothesis X] + [Subsingleton ω]`. -/
instance instHasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega
    [UniformizationGenus0Hypothesis X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasPic0AnalyticEquiv X :=
  hasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega

end JacobianChallenge

end
