/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearFirstRelationGenusOne
import JacobianChallenge.Manifold.StandardSymplecticForm
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus

set_option linter.unusedSectionVars false

/-! # `RiemannBilinearFirstRelation` on `T_L` UNCONDITIONAL (chip 20k)

Specializes chip 13 (`riemannBilinearFirstRelation_of_antisymmetric_genus_one`)
to the complex torus `T_L = ℂ ⧸ L`. Since `genus T_L = 1` is in tree
unconditionally (`ComplexTorus.genus_eq_one`) and the standard
symplectic form is anti-symmetric (`standardSymplectic_antisymm`),
the first relation holds with no further input.

Together with the chip 19 chain's unconditional second relation on
T_L (via chip 19r/t), this completes the *full* Riemann bilinear
content on T_L unconditionally.

## What this file ships

* `riemannBilinearFirstRelation_complexTorus_unconditional` — the
  T_L specialization.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`RiemannBilinearFirstRelation` on `T_L` UNCONDITIONAL** for any
choice of `data`, `basis_ω`, `cycleGens`, with `J := standardSymplectic 1`.

Composes:

* `ComplexTorus.genus_eq_one L` (`genus (ℂ ⧸ L) = 1`, unconditional);
* `standardSymplectic_antisymm` (anti-symmetry of the standard
  symplectic form);
* `riemannBilinearFirstRelation_of_antisymmetric_genus_one` (chip 13). -/
theorem riemannBilinearFirstRelation_complexTorus_unconditional
    (data : PeriodPairingData (ℂ ⧸ L))
    (basis_ω : Basis (Fin (JacobianChallenge.genus (ℂ ⧸ L))) ℂ
      (HolomorphicOneForm (ℂ ⧸ L)))
    (cycleGens : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) → data.H1) :
    RiemannBilinearFirstRelation data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus (ℂ ⧸ L))) := by
  exact riemannBilinearFirstRelation_of_antisymmetric_genus_one
    data basis_ω cycleGens
    (standardSymplectic_antisymm _)
    (genus_eq_one L)

end ComplexTorus

end JacobianChallenge

end
