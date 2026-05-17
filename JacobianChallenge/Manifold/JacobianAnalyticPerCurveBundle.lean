/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardPullbackContMDiff
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveContMDiff

/-! # Per-curve bundle for items 18 and 21 (pushforward/pullback ContMDiff)

OPEN.md items 18 (`pushforward_contMDiff`) and 21 (`pullback_contMDiff`)
require, for each holomorphic non-constant `f : X → Y`:

1. A ℂ-linear cover lift `T_f : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus Y) → ℂ)`
   (pushforward direction) or `T_f^* : (Fin (genus Y) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)`
   (pullback direction).
2. The lattice-matching condition: `T_f` carries the period image
   of `X` (against a basis `α_X`) into the period image of `Y`
   (against a basis `α_Y`).
3. (Optional, but commonly required.) Compatibility with the
   pointwise Abel-Jacobi maps: `T_f ∘ abelJacobiPoint_X = abelJacobiPoint_Y ∘ f`.

The construction of `T_f` is genuine analytic content (induced by the
pullback of holomorphic 1-forms, `f^* : H⁰(Y, Ω) → H⁰(X, Ω)`, with the
matrix coefficients being period integrals over chosen bases). It is
*not* discharged in this file. Instead, we surface the data as a
**named-hypothesis bundle** so downstream callers can supply specific
`f`s with concrete `T_f` constructions, and immediately get
`ContMDiff` of the induced pushforward/pullback at the
analytic-Jacobian level via
`analyticJacobian_linearLift_contMDiff`.

## Bundle layout

* `JacobianAnalyticPushforwardLift` — bundles a curve `f : X → Y` plus
  the linear lift `T_f` and the lattice-matching certificate. Optional
  Abel-Jacobi compatibility field.
* `JacobianAnalyticPullbackLift` — same with directions flipped.

Both bundles' `contMDiff` field is `analyticJacobian_linearLift_contMDiff`,
not a hypothesis: once the linear lift is provided, the smoothness is
automatic. This file therefore *closes* the OPEN-content portion of
items 18 and 21 modulo the per-curve construction.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

/-- **Per-curve pushforward bundle.** Carries:

* a holomorphic non-constant curve map `f : X → Y` (the smoothness
  certificate is `hf`);
* a ℂ-linear cover lift `T` from the period space of `X` to that of `Y`,
  carrying `data_X`'s lattice into `data_Y`'s.

The `ContMDiff` conclusion is automatic from
`analyticJacobian_linearLift_contMDiff`. -/
structure JacobianAnalyticPushforwardLift
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule] where
  /-- The underlying curve map. -/
  f : X → Y
  /-- Holomorphicity of `f`. -/
  contMDiff_f : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f
  /-- ℂ-linear cover lift, pushforward direction. -/
  T : (Fin (JacobianChallenge.genus X) → ℂ) →L[ℂ]
        (Fin (JacobianChallenge.genus Y) → ℂ)
  /-- The lift carries `data_X.lattice` into `data_Y.lattice`. -/
  lattice_match : ∀ x ∈ data_X.lattice.toIntSubmodule,
    T x ∈ data_Y.lattice.toIntSubmodule

/-- **Per-curve pullback bundle.** Same as pushforward with the linear
lift in the opposite direction. -/
structure JacobianAnalyticPullbackLift
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule] where
  f : X → Y
  contMDiff_f : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f
  /-- ℂ-linear cover lift, pullback direction. -/
  T : (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
        (Fin (JacobianChallenge.genus X) → ℂ)
  /-- The lift carries `data_Y.lattice` into `data_X.lattice`. -/
  lattice_match : ∀ x ∈ data_Y.lattice.toIntSubmodule,
    T x ∈ data_X.lattice.toIntSubmodule

namespace JacobianAnalyticPushforwardLift

variable {data_X : PeriodLatticeOfRankTwoG X}
  {data_Y : PeriodLatticeOfRankTwoG Y}
  [DiscreteTopology data_X.lattice.toIntSubmodule]
  [IsZLattice ℝ data_X.lattice.toIntSubmodule]
  [DiscreteTopology data_Y.lattice.toIntSubmodule]
  [IsZLattice ℝ data_Y.lattice.toIntSubmodule]

/-- The induced AnalyticJacobian-level pushforward map. -/
noncomputable def toQuotientMap
    (lift : JacobianAnalyticPushforwardLift data_X data_Y) :
    JacobianOfLattice X data_X → JacobianOfLattice Y data_Y :=
  quotientLinearMap data_X.lattice.toIntSubmodule
    data_Y.lattice.toIntSubmodule lift.T lift.lattice_match

/-- **Item 18 closure (analytic-Jacobian level):** the AnalyticJacobian-
level pushforward map is `ContMDiff`. -/
theorem toQuotientMap_contMDiff
    (lift : JacobianAnalyticPushforwardLift data_X data_Y) :
    haveI : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
          (JacobianOfLattice X data_X) :=
      chartedSpace_quotient_of_zlattice data_X.lattice.toIntSubmodule
    haveI : ChartedSpace (Fin (JacobianChallenge.genus Y) → ℂ)
          (JacobianOfLattice Y data_Y) :=
      chartedSpace_quotient_of_zlattice data_Y.lattice.toIntSubmodule
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ)) ω
      lift.toQuotientMap :=
  analyticJacobian_linearLift_contMDiff data_X data_Y lift.T lift.lattice_match

end JacobianAnalyticPushforwardLift

namespace JacobianAnalyticPullbackLift

variable {data_X : PeriodLatticeOfRankTwoG X}
  {data_Y : PeriodLatticeOfRankTwoG Y}
  [DiscreteTopology data_X.lattice.toIntSubmodule]
  [IsZLattice ℝ data_X.lattice.toIntSubmodule]
  [DiscreteTopology data_Y.lattice.toIntSubmodule]
  [IsZLattice ℝ data_Y.lattice.toIntSubmodule]

/-- The induced AnalyticJacobian-level pullback map. -/
noncomputable def toQuotientMap
    (lift : JacobianAnalyticPullbackLift data_X data_Y) :
    JacobianOfLattice Y data_Y → JacobianOfLattice X data_X :=
  quotientLinearMap data_Y.lattice.toIntSubmodule
    data_X.lattice.toIntSubmodule lift.T lift.lattice_match

/-- **Item 21 closure (analytic-Jacobian level):** the AnalyticJacobian-
level pullback map is `ContMDiff`. -/
theorem toQuotientMap_contMDiff
    (lift : JacobianAnalyticPullbackLift data_X data_Y) :
    haveI : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
          (JacobianOfLattice X data_X) :=
      chartedSpace_quotient_of_zlattice data_X.lattice.toIntSubmodule
    haveI : ChartedSpace (Fin (JacobianChallenge.genus Y) → ℂ)
          (JacobianOfLattice Y data_Y) :=
      chartedSpace_quotient_of_zlattice data_Y.lattice.toIntSubmodule
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
      lift.toQuotientMap :=
  analyticJacobian_linearLift_contMDiff data_Y data_X lift.T lift.lattice_match

end JacobianAnalyticPullbackLift

end JacobianChallenge

end
