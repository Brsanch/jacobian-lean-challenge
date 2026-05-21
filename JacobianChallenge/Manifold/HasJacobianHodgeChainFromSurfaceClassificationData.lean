/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChain
import JacobianChallenge.Manifold.HasSurfaceClassificationData
import JacobianChallenge.Manifold.CompleteHodgeRiemannGenusZero

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain` from `HasSurfaceClassificationData` + CHRH

`HasJacobianHodgeChain X` bundles five atoms:

* a basis `basis_ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`
* `basePoint : X`
* `symplecticBasis`
* `SmoothHurewiczHypothesis symplecticBasis`
* `CompleteHodgeRiemannHypothesis (...) basis_ω symplecticBasis.cycleGens`

Atoms 2, 3, 4 are exactly the content of `SurfaceClassificationData X`
(chips 1–3). This file ships the bridge constructor that combines a
`SurfaceClassificationData X` + a basis + the matching CHRH on
`scd.symplecticBasis.cycleGens` to discharge `HasJacobianHodgeChain X`.

Composed with the existing instance
`instHasJacobianAnalyticStructure_of_HasJacobianHodgeChain`, this
factors the user-visible content of `HasJacobianAnalyticStructure X`
into **two named classical bundles**:

* `[HasSurfaceClassificationData X]` — topological surface
  classification + smooth-Hurewicz.
* `CompleteHodgeRiemannHypothesis (...) basis_ω
  scd.symplecticBasis.cycleGens` — the chip-19/20 Hodge bilinear
  content (which on RS and T_L is unconditional, and at general genus
  is reduced to anti-sym `J` + strict-upper-triangular zeros + matrix
  PD via chip 20p).

## What this file ships

* `HasJacobianHodgeChain.ofSurfaceClassificationData` — explicit
  constructor.
* `HasJacobianHodgeChain.ofSurfaceClassificationData_genusZero` —
  vacuous CHRH discharge at `genus X = 0`: any `[HasSurfaceClassification
  Data X]` + `genus X = 0` discharges `HasJacobianHodgeChain X` via
  `completeHodgeRiemannHypothesis_of_genus_eq_zero`.
* `instHasJacobianHodgeChain_RiemannSphere_via_SCD` — smoke test on
  RS via the SCD-genus-zero route.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Explicit constructor: `SurfaceClassificationData X` + basis +
matching CHRH → `HasJacobianHodgeChain X`.**

Bundles the SCD's three topological / homological atoms with a chosen
ℂ-basis of `HolomorphicOneForm X` and the CHRH atom on the basis +
SCD's cycleGens. -/
theorem HasJacobianHodgeChain.ofSurfaceClassificationData
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (chrh :
      CompleteHodgeRiemannHypothesis
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        scd.symplecticBasis.cycleGens) :
    HasJacobianHodgeChain X :=
  ⟨basis_ω, scd.basePoint, scd.symplecticBasis, scd.hurewicz, chrh⟩

/-- **Constructor at `genus X = 0`: any `SurfaceClassificationData X`
+ `genus X = 0` discharges `HasJacobianHodgeChain X`.**

The CHRH atom is vacuous at genus 0 via
`completeHodgeRiemannHypothesis_of_genus_eq_zero`, so the only inputs
are the SCD and a basis. -/
theorem HasJacobianHodgeChain.ofSurfaceClassificationData_genusZero
    (scd : SurfaceClassificationData X)
    (h_genus : JacobianChallenge.genus X = 0)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    HasJacobianHodgeChain X :=
  HasJacobianHodgeChain.ofSurfaceClassificationData scd basis_ω
    (completeHodgeRiemannHypothesis_of_genus_eq_zero h_genus
      (PeriodPairingData.ofSmoothCycle X) basis_ω
      scd.symplecticBasis.cycleGens)

/-- **Typeclass form: `[HasSurfaceClassificationData X]` + `genus X = 0`
+ a basis discharges `HasJacobianHodgeChain X`.** -/
theorem HasJacobianHodgeChain.of_HasSurfaceClassificationData_genusZero
    [HasSurfaceClassificationData X]
    (h_genus : JacobianChallenge.genus X = 0)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    HasJacobianHodgeChain X :=
  HasJacobianHodgeChain.ofSurfaceClassificationData_genusZero
    (canonicalSurfaceClassificationData X) h_genus basis_ω

/-! ## Smoke test: RS via SCD-genus-zero route -/

namespace RiemannSphere

/-- **Smoke test: `HasJacobianHodgeChain RiemannSphere` via the
SCD-genus-zero route.**

Composes the unconditional `[HasSurfaceClassificationData RS]`
(chip 3) with `genus_RiemannSphere_eq_zero` and the default basis to
build `HasJacobianHodgeChain RS` through chip 4's constructor.
Reproduces the in-tree
`instHasJacobianHodgeChain_RiemannSphere` (which routes through the
direct genus-zero discharge) by an independent path. -/
theorem hasJacobianHodgeChain_RiemannSphere_via_SCD :
    HasJacobianHodgeChain RiemannSphere :=
  HasJacobianHodgeChain.of_HasSurfaceClassificationData_genusZero
    (X := RiemannSphere) genus_RiemannSphere_eq_zero
    (defaultHolomorphicOneFormBasis RiemannSphere)

end RiemannSphere

end JacobianChallenge

end
