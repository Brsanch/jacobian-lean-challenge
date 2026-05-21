/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackage
import JacobianChallenge.Manifold.SmoothHomologyDataPackageRiemannSphere

set_option linter.unusedSectionVars false

/-! # `SurfaceClassificationData X` — topological / homological atoms bundle

`SmoothHomologyDataPackage basis_ω` packages **four** atoms:

* `basePoint : X`
* `symplecticBasis : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (genus X)`
* `hurewicz : SmoothHurewiczHypothesis symplecticBasis`
* `bilinear : LinearIndependent ℝ (period vectors)`

The first three atoms are **purely topological / homological**: they
encode the structure of a compact connected oriented topological
2-manifold of genus `g` together with a chosen smooth symplectic
basis of `π₁^{smooth}(X, basePoint)` (equivalently, of `H₁(X; ℤ)` via
smooth-Hurewicz). Their classical source is the **topological surface
classification theorem** together with the smooth-Hurewicz theorem on
a closed orientable surface.

The fourth atom `bilinear` is the **Hodge bilinear non-degeneracy** —
ℝ-linear independence of the `2g` period vectors against a fixed
holomorphic 1-form basis. The chip-19/20 arc reduces this to a sharp
matrix-PD bundle (`CompleteHodgeRiemann*.lean`).

This file factors the first three atoms into a single named record
`SurfaceClassificationData X` (basis-agnostic) and ships:

* `SurfaceClassificationData X` — the bundle.
* `SurfaceClassificationData.toSmoothHomologyDataPackage` — bridge to
  `SmoothHomologyDataPackage basis_ω` consuming the chip-19/20
  `bilinear` atom against any `basis_ω`.
* `surfaceClassificationData_RiemannSphere p₀` — unconditional
  inhabitant on `RS` via the existing genus-0 empty-basis discharge.
* `nonempty_surfaceClassificationData_RiemannSphere` — `Nonempty`
  packaging.
* `nonempty_smoothHomologyDataPackage_RiemannSphere_via_SCD` — smoke
  test verifying the bridge reproduces the in-tree
  `SmoothHomologyDataPackage` on `RS`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SurfaceClassificationData X`** — bundle of the three named atoms
of `SmoothHomologyDataPackage` backed by the topological surface
classification theorem and smooth-Hurewicz.

Combining a `SurfaceClassificationData X` with a `bilinear`
non-degeneracy hypothesis (against any chosen ℂ-basis `basis_ω` of
`HolomorphicOneForm X`) yields a `SmoothHomologyDataPackage basis_ω`
via `toSmoothHomologyDataPackage`. -/
structure SurfaceClassificationData (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] where
  /-- A chosen base point of `X`. -/
  basePoint : X
  /-- A smooth symplectic basis of based loops at `basePoint` — the
  choice of `2g` based loops representing a symplectic homology basis
  of `H₁(X; ℤ)`. -/
  symplecticBasis :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X)
  /-- Smooth-Hurewicz on the chosen basis: every smooth based loop is
  a ℤ-combination of basis loops modulo a Stokes-boundary. -/
  hurewicz : SmoothHurewiczHypothesis symplecticBasis

namespace SurfaceClassificationData

variable (scd : SurfaceClassificationData X)

/-- **Bridge to `SmoothHomologyDataPackage basis_ω`.**

Combines the three topological / homological atoms (carried by `scd`)
with the Hodge bilinear-non-degeneracy atom against a chosen `basis_ω`.
The latter is the chip-19/20 content. -/
noncomputable def toSmoothHomologyDataPackage
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (bilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis_ω
            (scd.symplecticBasis.cycleGens i))) :
    SmoothHomologyDataPackage basis_ω where
  basePoint := scd.basePoint
  symplecticBasis := scd.symplecticBasis
  hurewicz := scd.hurewicz
  bilinear := bilinear

end SurfaceClassificationData

/-! ## Unconditional inhabitant on `RiemannSphere` -/

namespace RiemannSphere

/-- **Unconditional `SurfaceClassificationData` on `RiemannSphere`.**
At genus 0 the symplectic basis is empty (`Fin (2 * 0) = Fin 0`) and
smooth-Hurewicz on the empty basis reduces to
`basedSmoothLoopsBoundHypothesis_RS_holds`. -/
noncomputable def surfaceClassificationData_RiemannSphere
    (p₀ : RiemannSphere) :
    SurfaceClassificationData RiemannSphere where
  basePoint := p₀
  symplecticBasis := emptySymplecticBasis_RS p₀
  hurewicz := smoothHurewiczHypothesis_emptySymplecticBasis_RS p₀

/-- **`Nonempty (SurfaceClassificationData RiemannSphere)`.** Base
point chosen via `Classical.arbitrary`. -/
theorem nonempty_surfaceClassificationData_RiemannSphere :
    Nonempty (SurfaceClassificationData RiemannSphere) :=
  ⟨surfaceClassificationData_RiemannSphere (Classical.arbitrary _)⟩

/-- **Smoke test: the bridge through `SurfaceClassificationData`
reproduces the in-tree `SmoothHomologyDataPackage` on `RS`.**

Confirms that `SurfaceClassificationData` + `bilinear` (here
`linearIndependent_empty_type` on the genus-0 empty index set) yields
a `Nonempty (SmoothHomologyDataPackage basis_ω)` for any
`basis_ω : Basis (Fin (genus RS)) ℂ (HolomorphicOneForm RS)`,
matching `nonempty_smoothHomologyDataPackage_RiemannSphere`. -/
theorem nonempty_smoothHomologyDataPackage_RiemannSphere_via_SCD
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere)) :
    Nonempty (SmoothHomologyDataPackage (X := RiemannSphere) basis_ω) :=
  ⟨(surfaceClassificationData_RiemannSphere
      (Classical.arbitrary _)).toSmoothHomologyDataPackage
    linearIndependent_empty_type⟩

end RiemannSphere

end JacobianChallenge

end
