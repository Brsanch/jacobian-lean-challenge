/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RRGenusZeroGermComposition
import JacobianChallenge.Topology.Item14FinalComposition
import JacobianChallenge.Manifold.SurjectiveOfNonConstantDischarge
import JacobianChallenge.Manifold.BijectiveAnalyticDischarge
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional

set_option diagnostics.threshold 100

/-! # Item 14 closure from **two** named classical inputs

The germfield-arc capstone. With the previous chips landed, item 14's
final biconditional `genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)` reduces
to exactly **two** named classical inputs:

  1. `RR_DimGE2_GenusZero_Germ X` — the classical Riemann-Roch
     hypothesis on the germ field. Replaces the broken
     `RiemannRochGenusZero X` + `LiftToMeromorphicNonzero X` pair from
     `Topology/Item14FinalComposition.lean`'s 5-input chain, with the
     pointwise `linearSystemDeltaP` ambient swapped for the honest
     germ-quotient `linearSystemGermDeltaP` (see commit history of
     `germfield-arc-1` for the architectural reasoning).

  2. `h_top : Nonempty (X ≃ₜ StandardS2) → Nonempty (HolomorphicEquiv
     X RS)` — the topological-sphere half of uniformization.

All three previously-named conditionals
(`ramificationSumEqualsDegree_statement`,
`Surjective_of_NonConstant_Analytic_Manifold`,
`BijectiveAnalyticIsBiholomorphism`) are now **unconditional theorems**
in this repository, so they no longer appear as Prop hypotheses in the
signature:

* `JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree
  _holds_unconditional` (`Manifold/NearbyRegularWitnessUnconditional`).
* `JacobianChallenge.surjective_of_NonConstant_Analytic_Manifold_holds`
  (`Manifold/SurjectiveOfNonConstantDischarge`, zz382).
* `JacobianChallenge.bijectiveAnalyticIsBiholomorphism_holds`
  (`Manifold/BijectiveAnalyticDischarge`, zz388).

The germ-side RR composition discharges the pair (Riemann-Roch + lift)
via:

* `JacobianChallenge.MeromorphicFunctionField.
  riemannRochGenusZero_from_RR_DimGE2_Germ` (chip 5e of
  `germfield-arc-1`).

So this final composition simply plugs all the unconditionals into
`Topology/Item14FinalComposition.lean`'s
`genus_eq_zero_iff_homeo_from_all_conditionals`, leaving only the
two named hypotheses above.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from two named classical inputs.** The
maximally-compressed form of `genus_eq_zero_iff_homeo` currently
achievable in this repository: only `RR_DimGE2_GenusZero_Germ` and
the topological-sphere uniformization remain as Prop hypotheses; all
other previously-named inputs are discharged unconditionally. -/
theorem genus_eq_zero_iff_homeo_from_RR_DimGE2_Germ_and_top
    (hRR_germ : RR_DimGE2_GenusZero_Germ X)
    (h_top : Nonempty (X ≃ₜ JacobianChallenge.StandardS2) →
      Nonempty (JacobianChallenge.HolomorphicEquiv X
        JacobianChallenge.RiemannSphere)) :
    JacobianChallenge.genus X = 0 ↔
      Nonempty (X ≃ₜ JacobianChallenge.StandardS2) :=
  JacobianChallenge.genus_eq_zero_iff_homeo_from_all_conditionals
    (riemannRochGenusZero_from_RR_DimGE2_Germ X hRR_germ)
    (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
      X JacobianChallenge.RiemannSphere)
    (JacobianChallenge.surjective_of_NonConstant_Analytic_Manifold_holds
      (X := X) (Y := JacobianChallenge.RiemannSphere))
    (JacobianChallenge.bijectiveAnalyticIsBiholomorphism_holds (X := X))
    h_top

end JacobianChallenge.MeromorphicFunctionField

end
