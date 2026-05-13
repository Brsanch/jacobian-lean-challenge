/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneBijective
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphism
import JacobianChallenge.Manifold.HolomorphicEquivDegreeFiber
import JacobianChallenge.Topology.UniformizationFromRiemannRoch
import JacobianChallenge.Topology.Item14FromSingleUniformization

set_option diagnostics.threshold 100

/-! # Item 14 final closure composition

This file ships the **final composition** of all named conditional
hypotheses landed across zz309–zz330 into a single theorem stating
how item 14 closes from explicit classical inputs.

## The four named classical inputs

  1. `ramificationSumEqualsDegree_statement X RS` — sum of ram indices
     over a fibre equals the degree (existing, conditional on
     `NearbyRegularWitnessHypothesis`).
  2. `Surjective_of_NonConstant_Analytic_Manifold X RS` — non-constant
     ω-smooth maps are surjective (zz328).
  3. `BijectiveAnalyticIsBiholomorphism X` — bijective ω-smooth maps
     upgrade to biholomorphisms (zz330).
  4. `RiemannRochGenusZero X` — Riemann-Roch produces a degree-1
     meromorphic function on genus-0 surfaces (zz325).

Plus the topological-sphere half of `UniformizationToRiemannSphere`:

  5. `Nonempty (X ≃ₜ StandardS2) → Nonempty (HolomorphicEquiv X RS)` —
     uniformization for topological spheres.

## What ships here

* `degreeOneIsBiholomorphic_RS_of_conditionals` — chains conditionals
  1, 2, 3 to close zz325's `DegreeOneIsBiholomorphic_RS X`.
* `uniformizationToRiemannSphere_of_all_conditionals` — chains
  conditionals 1, 2, 3, 4, 5 to close zz309's
  `UniformizationToRiemannSphere X`.
* `genus_eq_zero_iff_homeo_from_all_conditionals` — the headline
  biconditional of item 14 from the five named classical inputs.

This is the maximally-compressed closure chain at the current pin:
five named classical theorems (none in mathlib), all explicit, all
referenced to standard textbooks. The Lean composition is mechanical.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`DegreeOneIsBiholomorphic_RS X` from three named conditionals.** -/
theorem degreeOneIsBiholomorphic_RS_of_conditionals
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement
      X JacobianChallenge.RiemannSphere)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold
      X JacobianChallenge.RiemannSphere)
    (h_bij : BijectiveAnalyticIsBiholomorphism.{u, 0} X) :
    DegreeOneIsBiholomorphic_RS X := by
  intro f hf hnc h_deg
  have hbij : Function.Bijective f :=
    bijective_of_degreeFiber_eq_one h_RS h_surj hf hnc h_deg
  exact h_bij f hf hbij

/-- **`UniformizationToRiemannSphere X` from all named conditionals.** -/
theorem uniformizationToRiemannSphere_of_all_conditionals
    (hRR : RiemannRochGenusZero X)
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement
      X JacobianChallenge.RiemannSphere)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold
      X JacobianChallenge.RiemannSphere)
    (h_bij : BijectiveAnalyticIsBiholomorphism.{u, 0} X)
    (h_top : Nonempty (X ≃ₜ StandardS2) →
      Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)) :
    UniformizationToRiemannSphere X := by
  intro h
  rcases h with hg | hHomeo
  · -- genus X = 0 branch: use Riemann-Roch + degree-1-is-biholomorphism.
    exact uniformizationToRiemannSphere_genus_zero_branch_from_RR X hRR
      (degreeOneIsBiholomorphic_RS_of_conditionals h_RS h_surj h_bij) hg
  · -- topological-sphere branch: use uniformization-for-spheres.
    exact h_top hHomeo

/-- **Item 14 biconditional from all named conditionals.** -/
theorem genus_eq_zero_iff_homeo_from_all_conditionals
    (hRR : RiemannRochGenusZero X)
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement
      X JacobianChallenge.RiemannSphere)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold
      X JacobianChallenge.RiemannSphere)
    (h_bij : BijectiveAnalyticIsBiholomorphism.{u, 0} X)
    (h_top : Nonempty (X ≃ₜ StandardS2) →
      Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere
    (uniformizationToRiemannSphere_of_all_conditionals hRR h_RS h_surj h_bij h_top)

end JacobianChallenge

end
