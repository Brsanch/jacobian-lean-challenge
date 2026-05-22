/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.UniformizationGenus0Hypothesis
import JacobianChallenge.Topology.Item14FinalComposition
import JacobianChallenge.Topology.UniformizationFromRiemannRoch
import JacobianChallenge.Manifold.SurjectiveOfNonConstantDischarge
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphismDischarge
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional

/-! # `UniformizationGenus0Hypothesis X` from `RiemannRochGenusZero X`

The shared C3 ↔ Item-14 atom `UniformizationGenus0Hypothesis X`
(`Topology/UniformizationGenus0Hypothesis.lean`) is **dischargeable
from** `RiemannRochGenusZero X` alone, by composing with the three
unconditional in-tree atoms:

* `ramificationSumEqualsDegree_holds_unconditional X RiemannSphere`
* `surjective_of_NonConstant_Analytic_Manifold_holds`
* `bijectiveAnalyticIsBiholomorphism_holds`

(The same three atoms used by today's
`genus_eq_zero_iff_homeo_from_2_minimal_classical_inputs`.) The
mathematical content is:

* RR at genus 0 ⇒ ∃ a non-constant `f : X → RS` of `degreeFiber = 1`
  (the `RiemannRochGenusZero` hypothesis literally states this);
* `bijective_of_degreeFiber_eq_one` (unconditional) + the bijective-
  analytic-is-biholomorphism atom ⇒ `Nonempty (HolomorphicEquiv X RS)`.

So `RiemannRochGenusZero X` is the **single classical content** behind
the shared atom on the C3 side. Closing genus-0 RR for general X
simultaneously closes the C3 genus-0 corner *and* the Item-14 forward
disjunct.

Headline:

```
theorem UniformizationGenus0Hypothesis.of_RiemannRochGenusZero
    (hRR : RiemannRochGenusZero X) :
    UniformizationGenus0Hypothesis X
```

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`UniformizationGenus0Hypothesis X` from `RiemannRochGenusZero X`.**

Composes the in-tree
`uniformizationToRiemannSphere_genus_zero_branch_from_RR` with the
unconditional discharge of `DegreeOneIsBiholomorphic_RS X` from the
three Item-14 unconditional atoms (`degreeOneIsBiholomorphic_RS_of_
conditionals` fed with `ramificationSumEqualsDegree_holds_uncondi-
tional`, `surjective_of_NonConstant_Analytic_Manifold_holds`,
`bijectiveAnalyticIsBiholomorphism_holds`).

This is the substantive content of the shared atom: every step beyond
`RiemannRochGenusZero X` is unconditional in tree. -/
theorem UniformizationGenus0Hypothesis.of_RiemannRochGenusZero
    (hRR : RiemannRochGenusZero X) :
    UniformizationGenus0Hypothesis X where
  out :=
    uniformizationToRiemannSphere_genus_zero_branch_from_RR X hRR
      (degreeOneIsBiholomorphic_RS_of_conditionals
        (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
          X JacobianChallenge.RiemannSphere)
        (surjective_of_NonConstant_Analytic_Manifold_holds
          (X := X) (Y := JacobianChallenge.RiemannSphere))
        (bijectiveAnalyticIsBiholomorphism_holds.{u, 0} X))

end JacobianChallenge

end
