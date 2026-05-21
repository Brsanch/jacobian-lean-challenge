/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainViaStandardForm
import JacobianChallenge.Manifold.CompleteHodgeRiemannViaStandardFormSubsingleton
import JacobianChallenge.Manifold.HasJacobianHodgeChain
import JacobianChallenge.Manifold.HasBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChainViaStandardForm` discharged at Subsingleton + HasBSLB
(chip 16)

Direct discharge of the simplified Hodge-chain class at genus 0
(`Subsingleton (HolomorphicOneForm X)`) + `[HasBasedSmoothLoopsBound X]`,
using chip 12's via-standard-form discharge instead of going through
the full Hodge chain.

This composes:
* `SmoothSymplecticBasis.emptyAtGenusZero` (chip 7's empty data).
* `smoothHurewicz_at_empty_basis` (chip 7's vacuous discharge).
* `completeHodgeRiemannHypothesisViaStandardForm_of_subsingleton` (chip
  12's auto-discharge of the simplified Hodge bundle at genus 0).

Result: `HasJacobianHodgeChainViaStandardForm.of_subsingleton_and_BSLB`
and (under `[HasBasedSmoothLoopsBound X]`) a typeclass-driven instance.

## What this file ships

* `HasJacobianHodgeChainViaStandardForm.of_subsingleton_and_BSLB` —
  data-style discharge.
* Theorem-form `instHasJacobianHodgeChainViaStandardForm_of_subsingleton_and_HasBSLB`
  — typeclass-driven discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Direct discharge of `HasJacobianHodgeChainViaStandardForm X` at
genus 0 + BSLB.** Combines the empty symplectic basis (chip 7) with
chip 12's via-standard-form discharge. -/
theorem HasJacobianHodgeChainViaStandardForm.of_subsingleton_and_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    HasJacobianHodgeChainViaStandardForm X := by
  refine ⟨defaultHolomorphicOneFormBasis X, basePoint,
    SmoothSymplecticBasis.emptyAtGenusZero basePoint,
    smoothHurewicz_at_empty_basis h_BSLB, ?_⟩
  exact completeHodgeRiemannHypothesisViaStandardForm_of_subsingleton _ _ _

/-- **Typeclass-driven discharge.** Not registered as a global `instance`
to avoid overlap with the chip 9 chain
(`Subsingleton + HasBSLB → HasJacobianHodgeChain` followed by
`HasJacobianHodgeChain → HasJacobianAnalyticStructure`). Downstream
consumers can invoke this explicitly when they specifically want the
via-standard-form route. -/
theorem hasJacobianHodgeChainViaStandardForm_of_subsingleton_and_HasBSLB
    [Subsingleton (HolomorphicOneForm X)]
    [hBSLB : HasBasedSmoothLoopsBound X] :
    HasJacobianHodgeChainViaStandardForm X := by
  obtain ⟨p₀, h_BSLB⟩ := hBSLB.out
  exact HasJacobianHodgeChainViaStandardForm.of_subsingleton_and_BSLB p₀ h_BSLB

end JacobianChallenge

end
