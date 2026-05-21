/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannGenusZero
import JacobianChallenge.Manifold.RiemannBilinearRelationsGenusZero
import JacobianChallenge.Manifold.RealLIPeriodVectorGenusZero
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # RiemannSphere smoke tests for chip 20a/b/c

`RiemannSphere` is the canonical genus-0 manifold:
`RiemannSphere.genus_RiemannSphere_eq_zero` is unconditional in
tree. Chip 20a (CHRH), 20b (RiemannBilinearRelations), and 20c
(ℝ-LI of period vectors) all reduce to vacuous bundles via the
`genus = 0` hypothesis, with no further input required.

This file provides end-to-end smoke tests confirming that the
chip 20a/b/c chain fires on `RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace RiemannSphere

/-! ## Chip 20a on RiemannSphere -/

/-- **CHRH unconditional on RiemannSphere via chip 20a.** -/
example
    (data : PeriodPairingData RiemannSphere)
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere))
    (cycleGens : Fin (2 * JacobianChallenge.genus RiemannSphere) →
      data.H1) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens :=
  completeHodgeRiemannHypothesis_of_genus_eq_zero
    genus_RiemannSphere_eq_zero data basis_ω cycleGens

/-! ## Chip 20b on RiemannSphere -/

/-- **RiemannBilinearRelations unconditional on RiemannSphere via chip 20b.** -/
example
    (data : PeriodPairingData RiemannSphere)
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere))
    (cycleGens : Fin (2 * JacobianChallenge.genus RiemannSphere) →
      data.H1) :
    RiemannBilinearRelations data basis_ω cycleGens :=
  riemannBilinearRelations_of_genus_eq_zero
    genus_RiemannSphere_eq_zero data basis_ω cycleGens

/-! ## Chip 20c on RiemannSphere -/

/-- **ℝ-LI of period vectors unconditional on RiemannSphere via chip 20c.** -/
example
    (data : PeriodPairingData RiemannSphere)
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere))
    (cycleGens : Fin (2 * JacobianChallenge.genus RiemannSphere) →
      data.H1) :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus RiemannSphere) =>
        periodVector data basis_ω (cycleGens i)) :=
  realLI_periodVector_of_genus_eq_zero
    genus_RiemannSphere_eq_zero data basis_ω cycleGens

end RiemannSphere

end JacobianChallenge

end
