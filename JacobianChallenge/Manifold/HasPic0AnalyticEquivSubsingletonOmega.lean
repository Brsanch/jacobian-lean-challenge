/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.HasPic0AnalyticEquivRiemannSphere
import JacobianChallenge.Manifold.Pic0SubsingletonBridge
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton

set_option linter.unusedSectionVars false

/-! # `HasPic0AnalyticEquiv X` from `[Subsingleton (HolomorphicOneForm X)]`

Generalises Phase B (`RiemannSphere`) to any compact connected complex
1-manifold `X` whose space of holomorphic 1-forms is a subsingleton.
This is the "genus-0 universally" discharge — both sides of the
Pic⁰ ↔ analytic-Jacobian bridge collapse to a singleton at genus 0, so
the AddEquiv is canonical.

The hypothesis `[Subsingleton (HolomorphicOneForm X)]` is unconditional
on `RiemannSphere` (`Manifold/RiemannSphereChartSCoeffOverlap.lean`
line 169) and on any X biholomorphic to RS, but is genuinely an extra
hypothesis at the general-X level.

## Why this requires `[HasSurfaceClassificationData X]` too

The `Pic0AnalyticEquivBundle`'s `shdp` field requires
`HasSmoothHomologyDataPackage X basis_ω` for our chosen `basis_ω`.
At genus 0, `basis_ω` is `Basis.empty` (vacuous), and the SHDP is
discharged via the unconditional genus-0 path
(`SmoothHomologyDataPackageSubsingleton` or similar). The cleanest
combined hypothesis here is `[HasSmoothHomologyDataPackage X
(Basis.empty _)]` which holds whenever there's some symplectic-basis
witness — currently in tree on RS and T_L. For X with subsingleton ω
but not necessarily one of those, we additionally request
`[HasSurfaceClassificationData X]` to get the witness via the
existing class plumbing.

## What this file ships

* `pic0AnalyticEquivBundle_of_subsingleton_omega` — constructor.
* `hasPic0AnalyticEquiv_of_subsingleton_omega` — theorem form
  (not declared `instance` to avoid typeclass loops).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The canonical `Basis (Fin 0) ℂ (HolomorphicOneForm X)` at
subsingleton ω.** Generalisation of `basisOmegaRiemannSphere`. At
subsingleton ω, the genus is 0 (via `Module.finrank_zero_of_subsingleton`
+ the unconditional finite-dim instance), so `Fin (genus X) = Fin 0` is
empty and `Basis.empty` applies. -/
noncomputable def basisOmegaOfSubsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  have hg : JacobianChallenge.genus X = 0 := by
    show Module.finrank ℂ (HolomorphicOneForm X) = 0
    exact Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [hg]; exact Fin.isEmpty
  exact Basis.empty _

/-- **The Pic⁰ ↔ analytic-Jacobian bundle from subsingleton ω +
subsingleton Pic⁰ + an SHDP witness.**

The three hypotheses are independent:
* `[Subsingleton (HolomorphicOneForm X)]` makes the analytic side
  subsingleton.
* `[Subsingleton (Pic0 X)]` makes the algebraic side subsingleton.
* The SHDP witness gives the `CanonicalAnalyticJacobian` its
  `ChartedSpace`/`LieAddGroup`/etc. instances.

The AddEquiv between two subsingleton AddZeroClasses is canonical
(via `RiemannSphere.addEquivOfSubsingletons`).

This is **the genus-0 universal discharge** of Phase A. -/
noncomputable def pic0AnalyticEquivBundle_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)]
    [HasSmoothHomologyDataPackage (X := X) (basisOmegaOfSubsingleton (X := X))] :
    Pic0AnalyticEquivBundle X := by
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_finGenusToComplex_of_subsingleton_omega (X := X)
  haveI :
      Subsingleton (CanonicalAnalyticJacobian (X := X)
        (basisOmegaOfSubsingleton (X := X))) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient
      (canonicalPeriodLatticeOfRankTwoG (basisOmegaOfSubsingleton (X := X)))
  exact
    { basis_ω := basisOmegaOfSubsingleton
      shdp := inferInstance
      equiv := RiemannSphere.addEquivOfSubsingletons }

/-- **`HasPic0AnalyticEquiv X` from subsingleton ω + subsingleton Pic⁰
+ an SHDP witness.** Theorem-form (not `instance` to avoid synthesis
ambiguity on `basisOmegaOfSubsingleton`). -/
theorem hasPic0AnalyticEquiv_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)]
    [HasSmoothHomologyDataPackage (X := X) (basisOmegaOfSubsingleton (X := X))] :
    HasPic0AnalyticEquiv X :=
  ⟨⟨pic0AnalyticEquivBundle_of_subsingleton_omega (X := X)⟩⟩

end JacobianChallenge

end
