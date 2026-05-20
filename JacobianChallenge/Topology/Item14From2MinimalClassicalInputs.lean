/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FinalComposition
import JacobianChallenge.Manifold.SurjectiveOfNonConstantDischarge
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphismDischarge
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional from 2 minimal classical inputs

Compresses `genus_eq_zero_iff_homeo_from_all_conditionals` (5 named
inputs) by discharging the 3 currently-unconditional named inputs:

* `ramificationSumEqualsDegree_statement` via
  `ramificationSumEqualsDegree_holds_unconditional`.
* `Surjective_of_NonConstant_Analytic_Manifold` via
  `surjective_of_NonConstant_Analytic_Manifold_holds`.
* `BijectiveAnalyticIsBiholomorphism` via
  `bijectiveAnalyticIsBiholomorphism_holds`.

The remaining **2 minimal classical inputs** are:

* `RiemannRochGenusZero X` (Riemann-Roch produces a degree-1
  meromorphic function on genus-0 surfaces — zz325).
* `h_top : Nonempty (X ≃ₜ StandardS2) → Nonempty (HolomorphicEquiv X RS)`
  (uniformization for topological spheres).

This is a parallel composition route to
`genus_eq_zero_iff_homeo_from_4_minimal_inputs`
(`Topology/Item14From4MinimalInputs.lean`), which takes a *different*
slice of named hypotheses (forward-leg `ExistsSimplePoleGermAtSomePoint`
+ reverse-leg `BasedSmoothLoopsBoundHypothesis` + per-basis primitive
smoothness/FTC). Both routes are valid; this file's route compresses
via the existing `Item14FinalComposition` chain.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from 2 minimal classical inputs** —
Riemann-Roch on genus 0 + topological-sphere uniformization.

Compared to `genus_eq_zero_iff_homeo_from_all_conditionals` (5 named
inputs), this composition discharges the three unconditional ones:

* `ramificationSumEqualsDegree_holds_unconditional X RiemannSphere`;
* `surjective_of_NonConstant_Analytic_Manifold_holds (X := X) (Y := RiemannSphere)`;
* `bijectiveAnalyticIsBiholomorphism_holds X`.

leaving only the two genuinely classical inputs. -/
theorem genus_eq_zero_iff_homeo_from_2_minimal_classical_inputs
    (hRR : RiemannRochGenusZero X)
    (h_top : Nonempty (X ≃ₜ StandardS2) →
      Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_all_conditionals
    hRR
    (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
      X JacobianChallenge.RiemannSphere)
    (surjective_of_NonConstant_Analytic_Manifold_holds
      (X := X) (Y := JacobianChallenge.RiemannSphere))
    (bijectiveAnalyticIsBiholomorphism_holds.{u, 0} X)
    h_top

end JacobianChallenge

end
