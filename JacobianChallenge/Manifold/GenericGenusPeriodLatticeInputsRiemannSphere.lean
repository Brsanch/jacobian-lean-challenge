/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputs
import JacobianChallenge.Manifold.StokesBoundariesRiemannSphereTop
import JacobianChallenge.Manifold.StokesCanonicalH1SubsingletonChar
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` on `RiemannSphere`, unconditional

Builds the full `GenericGenusPeriodLatticeInputs` structure for
`X = RiemannSphere`, with all four atomic inputs discharged
unconditionally:

* `cycleGens` — vacuous (`Fin (2 * genus RS) = Fin 0`); discharge via
  `Fin.elim0`-style.
* `riemannBilinear` — vacuously linearly independent on the empty tuple.
* `holomorphicCanonicalClosed` — via
  `HolomorphicComponentsCanonicalClosed.of_subsingleton` with the
  unconditional `Subsingleton (HolomorphicOneForm RS)` instance.
* `H1_spans_top_canonical` — via `Subsingleton (canonical H₁)` derived
  from `stokesBoundaries_RS_eq_top` (the chip we just proved).

## What this file ships

* `genericGenusPeriodLatticeInputs_RiemannSphere`
* `nonempty_genericGenusPeriodLatticeInputs_RiemannSphere`

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

namespace RiemannSphere

/-- **Unconditional `GenericGenusPeriodLatticeInputs` on `RS`.** All
four atomic inputs are discharged in tree (genus-0 specialisation). -/
noncomputable def genericGenusPeriodLatticeInputs_RiemannSphere
    (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    GenericGenusPeriodLatticeInputs (X := RiemannSphere) basis :=
  haveI : Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ)
      RiemannSphere).H1 :=
    subsingleton_canonical_H1_of_stokesBoundaries_eq_top stokesBoundaries_RS_eq_top
  haveI hempty : IsEmpty (Fin (2 * JacobianChallenge.genus RiemannSphere)) := by
    rw [genus_RiemannSphere_eq_zero, Nat.mul_zero]; infer_instance
  { cycleGens := hempty.elim
    riemannBilinear := linearIndependent_empty_type
    holomorphicCanonicalClosed :=
      HolomorphicComponentsCanonicalClosed.of_subsingleton
    H1_spans_top_canonical := Subsingleton.elim _ _ }

/-- **Nonempty version.** -/
theorem nonempty_genericGenusPeriodLatticeInputs_RiemannSphere
    (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    Nonempty (GenericGenusPeriodLatticeInputs (X := RiemannSphere) basis) :=
  ⟨genericGenusPeriodLatticeInputs_RiemannSphere basis⟩

end RiemannSphere

end JacobianChallenge

end
