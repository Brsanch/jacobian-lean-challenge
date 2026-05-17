/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingMorphismOfSmoothCycle
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackId

set_option linter.unusedSectionVars false

/-! # Identity-curve-map case of `PeriodPairingMorphism`

For the identity curve map `id : X → X`, the period-pairing morphism
(against the same `PeriodPairingData` on both sides) is the identity
on cycles, and the adjunction holds trivially because both pullback
and pushforward of cycles are identity operations and the period
pairing is symmetric in the obvious way.

This is the trivial-functoriality sanity check for the bundle. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- The identity curve map gives the identity cycle pushforward, with
trivial adjunction (pullback of forms along `id` is the identity). -/
noncomputable def PeriodPairingMorphism.id'_ofSmoothCycle :
    PeriodPairingMorphism (PeriodPairingData.ofSmoothCycle X)
                          (PeriodPairingData.ofSmoothCycle X) where
  f := _root_.id
  contMDiff_f := contMDiff_id
  cyclePush := AddMonoidHom.id (SmoothCycle 𝓘(ℝ, ℂ) X)
  adjunction := by
    intro γ τ
    -- Pairing is `complexPeriod`. Goal: complexPeriod γ τ = complexPeriod γ (pullback id τ).
    show complexPeriod γ τ = complexPeriod γ (HolomorphicOneForm.pullback _root_.id contMDiff_id τ)
    rw [HolomorphicOneForm.pullback_id]

end JacobianChallenge

end
