/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquivSubsingletonViaPhases
import JacobianChallenge.Manifold.HasPic0AnalyticEquivRiemannSphere
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # HasPic0AnalyticEquiv RiemannSphere via the full Phase E/F/G chain

Concrete smoke test: discharges `HasPic0AnalyticEquiv RiemannSphere`
via the **full Phase E + F + G chain modulo SHDP**, providing an
alternative to Phase B's direct `addEquivOfSubsingletons` proof.

The RS instance has:
* `Subsingleton (HolomorphicOneForm RiemannSphere)` —
  `Manifold/RiemannSphereChartSCoeffOverlap.lean` line 169.
* `Subsingleton (Pic0 RiemannSphere)` —
  `Manifold/Pic0RiemannSphereSubsingleton.lean` line 163.
* `instHasSmoothHomologyDataPackage_RiemannSphere` —
  `Manifold/SmoothHomologyDataPackageClass.lean` line 83.

All three feed into Frontier-6's
`hasPic0AnalyticEquiv_of_subsingleton_omega_pic0_via_phases`.

This validates that the entire Phase factorization actually composes
on a real-world example. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace RiemannSphere

/-- **HasPic0AnalyticEquiv RiemannSphere via the Phase E/F/G chain.**

Alternative to `instHasPic0AnalyticEquiv_RiemannSphere` (Phase B's
direct subsingleton-AddEquiv proof). Same conclusion, different route:

* Phase A scaffold + Phase G (modulo SHDP) build the bundle from
  a `Pic⁰ X ≃+ CanonicalAnalyticJacobian basis_ω` AddEquiv.
* The AddEquiv is built by `B.abelJacobiEquiv hAbel hJI` where
  Phase E discharges Abel (trivially via subsingleton ω) and Phase F
  discharges Jacobi inversion (injective via subsingleton Pic⁰,
  surjective via subsingleton ω).

This is a smoke test of the full architecture. Not declared as
`instance` to avoid overlap with the canonical Phase B instance. -/
theorem hasPic0AnalyticEquivRiemannSphere_via_phases :
    HasPic0AnalyticEquiv RiemannSphere := by
  haveI : Subsingleton (Pic0 RiemannSphere) := subsingleton_pic0_RiemannSphere
  haveI : HasSmoothHomologyDataPackage (X := RiemannSphere)
      JacobianChallenge.RiemannSphere.basisOmegaRiemannSphere :=
    inferInstance
  exact hasPic0AnalyticEquiv_of_subsingleton_omega_pic0_via_phases
    (X := RiemannSphere) JacobianChallenge.RiemannSphere.basisOmegaRiemannSphere

end RiemannSphere

end JacobianChallenge

end
