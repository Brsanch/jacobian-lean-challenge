/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackageRiemannSphere
import JacobianChallenge.Manifold.SmoothHomologyDataPackageComplexTorus

set_option linter.unusedSectionVars false

/-! # Typeclass wrapper `HasSmoothHomologyDataPackage`

Typeclass-friendly form of `Nonempty (SmoothHomologyDataPackage
basis_ω)`. Downstream consumers (period-lattice symplectic bundle
factories on items 5/11/12/13/17/18/21) can request the single bundled
period-lattice atom via `[HasSmoothHomologyDataPackage X basis_ω]`
instead of taking it as an explicit hypothesis.

## What this file ships

* `HasSmoothHomologyDataPackage X basis_ω` — `Prop`-valued class
  wrapping `Nonempty (SmoothHomologyDataPackage basis_ω)`.
* `instHasSmoothHomologyDataPackage_RiemannSphere` — instance on `RS`
  for any `basis_ω` (genus-0 unconditional discharge).
* `instHasSmoothHomologyDataPackage_complexTorus` — instance on `T_L`
  for the canonical `basis_g_dz L` (genus-1 unconditional discharge).
* `nonempty_periodLatticeSymplecticBundle_of_class` — typeclass-form
  composite producing `Nonempty (PeriodLatticeSymplecticBundle ...)`
  from `[HasSmoothHomologyDataPackage X basis_ω]`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Typeclass wrapper for `Nonempty (SmoothHomologyDataPackage
basis_ω)`.** Allows downstream consumers to request the period-lattice
atom as a typeclass hypothesis. -/
class HasSmoothHomologyDataPackage
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) : Prop where
  /-- Nonempty witness of `SmoothHomologyDataPackage basis_ω`. -/
  out : Nonempty (SmoothHomologyDataPackage basis_ω)

/-- **Extraction lemma:** under `[HasSmoothHomologyDataPackage X
basis_ω]`, the bundled period-lattice atom is nonempty. -/
theorem nonempty_smoothHomologyDataPackage_of_class
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    [h : HasSmoothHomologyDataPackage basis_ω] :
    Nonempty (SmoothHomologyDataPackage basis_ω) :=
  h.out

/-- **Typeclass-form composite:** `[HasSmoothHomologyDataPackage X
basis_ω]` ⟹ `Nonempty (PeriodLatticeSymplecticBundle ... basis_ω)`. -/
theorem nonempty_periodLatticeSymplecticBundle_of_class
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    [HasSmoothHomologyDataPackage basis_ω] :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X)
        basis_ω) :=
  nonempty_periodLatticeSymplecticBundle_of_nonempty_smoothHomologyDataPackage
    nonempty_smoothHomologyDataPackage_of_class

/-! ## Instance: `RiemannSphere` -/

namespace RiemannSphere

/-- **Unconditional instance for `RiemannSphere`** at any
`basis_ω : Basis (Fin (genus RiemannSphere)) ℂ (HolomorphicOneForm RiemannSphere)`.
Discharges via `nonempty_smoothHomologyDataPackage_RiemannSphere`
(genus-0 unconditional). -/
instance instHasSmoothHomologyDataPackage_RiemannSphere
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere)) :
    HasSmoothHomologyDataPackage (X := RiemannSphere) basis_ω where
  out := nonempty_smoothHomologyDataPackage_RiemannSphere basis_ω

end RiemannSphere

/-! ## Instance: `T_L = ℂ ⧸ L` -/

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Unconditional instance for the complex torus `T_L`** at the
canonical basis `basis_g_dz L`. Discharges via
`nonempty_smoothHomologyDataPackage_complexTorus` (genus-1 unconditional). -/
instance instHasSmoothHomologyDataPackage_complexTorus :
    HasSmoothHomologyDataPackage (X := ℂ ⧸ L) (basis_g_dz L) where
  out := nonempty_smoothHomologyDataPackage_complexTorus L

end ComplexTorus

end JacobianChallenge

end
