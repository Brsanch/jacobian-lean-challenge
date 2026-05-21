/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonFromBSLBAndPathPrimitive
import JacobianChallenge.Manifold.PathPrimitiveGlobalSmoothFTC

set_option linter.unusedSectionVars false

/-! # `Subsingleton (HolomorphicOneForm X)` from BSLB + universal admissibility

A further consolidation of `subsingleton_of_BSLB_and_pathPrimitive`
(in `Manifold/SubsingletonFromBSLBAndPathPrimitive.lean`) replacing
the universal-in-`om` `PathPrimitiveSmoothness` + `PathPrimitiveFTC`
hypotheses by their derivation from the per-form
`PathPrimitiveAdmissibleChartCover om` bundled admissibility predicate.

The chain:

* `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis` (universal,
  in `Manifold/LoopPeriodVanishesOfBasedSmoothLoopsBound.lean`) lifts
  BSLB to `AllLoopsVanish x₀` via chip D + 2-chain linearity.

* `pathPrimitive_contMDiff_of_admissible` and
  `pathPrimitive_eval_eq_mfderiv_of_admissible` (in
  `Manifold/PathPrimitiveGlobalSmoothFTC.lean`) discharge per-form
  smoothness + FTC from the admissibility predicate per `om`.

* `subsingleton_of_pathPrimitive_hypotheses` then closes
  `Subsingleton (HolomorphicOneForm X)`.

The single-statement consolidation is useful in contexts where
admissibility is supplied uniformly (e.g. by a `HasAdmissibleChartCover`
typeclass instance) rather than per-basis.

## What ships

* `pathPrimitiveSmoothness_of_BSLB_and_universalAdmissibility` —
  universal smoothness from BSLB + universal admissibility.
* `pathPrimitiveFTC_of_BSLB_and_universalAdmissibility` —
  universal FTC from the same.
* `subsingleton_of_BSLB_and_universalAdmissibility` —
  `Subsingleton (HolomorphicOneForm X)` from the bundled inputs.
* `holomorphicOneFormSubsingletonOfSimplyConnected_of_BSLB_and_universalAdmissibility`
  — `SimplyConnectedSpace`-conditional variant.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`PathPrimitiveSmoothness` from BSLB + universal admissibility.**

For each `om`, `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`
gives `LoopPeriodVanishes om x₀`. Combined with
`PathPrimitiveAdmissibleChartCover om`, `pathPrimitive_contMDiff_of_admissible`
yields smoothness. -/
theorem pathPrimitiveSmoothness_of_BSLB_and_universalAdmissibility
    {x₀ : X} (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : ∀ om : HolomorphicOneForm X,
      PathPrimitiveAdmissibleChartCover om) :
    PathPrimitiveSmoothness
      (smoothPathConnected_of_preconnected (X := X)) x₀ := fun om =>
  pathPrimitive_contMDiff_of_admissible
    (smoothPathConnected_of_preconnected (X := X)) x₀ om
    (loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis h_bslb om)
    (h_admit om)

/-- **`PathPrimitiveFTC` from BSLB + universal admissibility.** -/
theorem pathPrimitiveFTC_of_BSLB_and_universalAdmissibility
    {x₀ : X} (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : ∀ om : HolomorphicOneForm X,
      PathPrimitiveAdmissibleChartCover om) :
    PathPrimitiveFTC
      (smoothPathConnected_of_preconnected (X := X)) x₀ := fun om x =>
  pathPrimitive_eval_eq_mfderiv_of_admissible
    (smoothPathConnected_of_preconnected (X := X)) x₀ om
    (loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis h_bslb om)
    (h_admit om) x

/-- **`Subsingleton (HolomorphicOneForm X)` from BSLB + universal
admissibility.** Composes the two preceding theorems with
`subsingleton_of_BSLB_and_pathPrimitive`. -/
theorem subsingleton_of_BSLB_and_universalAdmissibility
    (x₀ : X) (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : ∀ om : HolomorphicOneForm X,
      PathPrimitiveAdmissibleChartCover om) :
    Subsingleton (HolomorphicOneForm X) :=
  subsingleton_of_BSLB_and_pathPrimitive x₀ h_bslb
    (pathPrimitiveSmoothness_of_BSLB_and_universalAdmissibility h_bslb h_admit)
    (pathPrimitiveFTC_of_BSLB_and_universalAdmissibility h_bslb h_admit)

/-- **`SimplyConnectedSpace`-conditional variant.** -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_BSLB_and_universalAdmissibility
    (x₀ : X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : SimplyConnectedSpace X → ∀ om : HolomorphicOneForm X,
      PathPrimitiveAdmissibleChartCover om) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X := fun h_sc =>
  subsingleton_of_BSLB_and_universalAdmissibility x₀ (h_bslb h_sc) (h_admit h_sc)

end JacobianChallenge

end
