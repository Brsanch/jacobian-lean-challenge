/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # `HasPic0AnalyticEquiv RiemannSphere` — Phase B (smoke test)

Discharges `HasPic0AnalyticEquiv RiemannSphere` unconditionally.

**Why it's trivial at genus 0**: both sides of the bridge AddEquiv are
subsingleton:

* `Subsingleton (Pic0 RiemannSphere)` —
  `Manifold/Pic0RiemannSphereSubsingleton.lean` line 163.
* `Subsingleton (CanonicalAnalyticJacobian basis_ω)` for `basis_ω :
  Basis (Fin 0) ℂ (HolomorphicOneForm RS)` — combines
  `subsingleton_jacobianOfLattice_of_subsingleton_ambient` (sister
  `CanonicalAnalyticJacobianSubsingleton.lean` line 69) with
  `subsingleton_finGenusToComplex_of_subsingleton_omega` (line 49) +
  the instance `Subsingleton (HolomorphicOneForm RiemannSphere)`
  (`Manifold/RiemannSphereChartSCoeffOverlap.lean` line 169).

So the AddEquiv is the canonical group iso between two singletons.

This is a smoke test of the Phase A architecture, not a `Basic.lean`
flip. Item 5 in `Basic.lean` is universally quantified over all `X`,
so a specific-`X` instance does not flip its sorry.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace RiemannSphere

/-- The canonical `Basis (Fin 0) ℂ (HolomorphicOneForm RiemannSphere)`.
At genus 0, the holomorphic-1-form space is subsingleton, so the empty
indexed family is vacuously a basis. -/
noncomputable def basisOmegaRiemannSphere :
    Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm RiemannSphere) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := RiemannSphere))
  have hg : JacobianChallenge.genus RiemannSphere = 0 := by
    show Module.finrank ℂ (HolomorphicOneForm RiemannSphere) = 0
    exact Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (JacobianChallenge.genus RiemannSphere)) := by
    rw [hg]; exact Fin.isEmpty
  exact Basis.empty _

/-- **Subsingleton-to-subsingleton `AddEquiv`.** Between two subsingleton
`AddZeroClass`es, the canonical equiv sending everything to `0`. -/
def addEquivOfSubsingletons {A B : Type*}
    [AddZeroClass A] [AddZeroClass B]
    [Subsingleton A] [Subsingleton B] :
    A ≃+ B where
  toFun := fun _ => 0
  invFun := fun _ => 0
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  map_add' := fun _ _ => Subsingleton.elim _ _

/-- **The Pic⁰ ↔ analytic-Jacobian bundle on `RiemannSphere`,
unconditional.** Both sides subsingleton, so the AddEquiv is canonical.
-/
noncomputable def pic0AnalyticEquivBundleRiemannSphere :
    Pic0AnalyticEquivBundle RiemannSphere := by
  haveI : Subsingleton (Pic0 RiemannSphere) := subsingleton_pic0_RiemannSphere
  haveI : Subsingleton (Fin (JacobianChallenge.genus RiemannSphere) → ℂ) :=
    subsingleton_finGenusToComplex_of_subsingleton_omega (X := RiemannSphere)
  refine
    { basis_ω := basisOmegaRiemannSphere
      shdp := inferInstance
      equiv := ?_ }
  haveI : HasSmoothHomologyDataPackage (X := RiemannSphere) basisOmegaRiemannSphere :=
    inferInstance
  haveI :
      Subsingleton (CanonicalAnalyticJacobian (X := RiemannSphere)
        basisOmegaRiemannSphere) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient
      (canonicalPeriodLatticeOfRankTwoG basisOmegaRiemannSphere)
  exact addEquivOfSubsingletons

/-- **Unconditional `HasPic0AnalyticEquiv RiemannSphere` instance.** -/
instance instHasPic0AnalyticEquiv_RiemannSphere :
    HasPic0AnalyticEquiv RiemannSphere where
  out := ⟨pic0AnalyticEquivBundleRiemannSphere⟩

end RiemannSphere

end JacobianChallenge

end
