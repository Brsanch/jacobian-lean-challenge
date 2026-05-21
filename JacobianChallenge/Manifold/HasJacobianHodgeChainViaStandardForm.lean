/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChain
import JacobianChallenge.Manifold.CompleteHodgeRiemannViaStandardForm

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChainViaStandardForm X` — class wrapper for the
simplified Hodge chain (chip 15)

Parallel class to `HasJacobianHodgeChain X` that uses the simplified
`CompleteHodgeRiemannHypothesisViaStandardForm` (chip 11) instead of
the full `CompleteHodgeRiemannHypothesis`. The PD atom and the Hodge
form choice are absorbed by the standard form.

Under this class, `HasJacobianHodgeChain X` is automatic via chip 11's
bridge `completeHodgeRiemannHypothesis_of_viaStandardForm`. Hence
`HasJacobianAnalyticStructure X` also follows.

## What this file ships

* `HasJacobianHodgeChainViaStandardForm` — the simplified class.
* `instance instHasJacobianHodgeChain_of_HasJacobianHodgeChainViaStandardForm`
  — bridge to the unsimplified class.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianHodgeChainViaStandardForm X` class.** Parallel to
`HasJacobianHodgeChain X` but uses the simplified Hodge bundle
`CompleteHodgeRiemannHypothesisViaStandardForm`. -/
class HasJacobianHodgeChainViaStandardForm (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- A basis, base point, symplectic basis, smooth-Hurewicz hypothesis,
  and via-standard-form Hodge bundle. -/
  out : ∃ (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
              (HolomorphicOneForm X))
          (basePoint : X)
          (symplecticBasis :
            SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint
              (JacobianChallenge.genus X)),
          SmoothHurewiczHypothesis symplecticBasis ∧
          CompleteHodgeRiemannHypothesisViaStandardForm
            (PeriodPairingData.ofSmoothCycle X) basis_ω
            symplecticBasis.cycleGens

/-- **Bridge: `HasJacobianHodgeChainViaStandardForm X ⟹ HasJacobianHodgeChain X`.**
Composes chip 11's `completeHodgeRiemannHypothesis_of_viaStandardForm`
to upgrade the simplified Hodge bundle into the full one. -/
instance instHasJacobianHodgeChain_of_HasJacobianHodgeChainViaStandardForm
    [h : HasJacobianHodgeChainViaStandardForm X] :
    HasJacobianHodgeChain X := by
  obtain ⟨basis_ω, basePoint, symplecticBasis, hurewicz, hHRStd⟩ := h.out
  refine ⟨basis_ω, basePoint, symplecticBasis, hurewicz, ?_⟩
  exact completeHodgeRiemannHypothesis_of_viaStandardForm hHRStd

end JacobianChallenge

end
