/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingMorphism
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackId

set_option linter.unusedSectionVars false

/-! # Identity functoriality of `PeriodPairingMorphism`

The general identity case — for any `data : PeriodPairingData X`, the
identity curve map `id : X → X` gives the identity period-pairing
morphism (cycle pushforward = `AddMonoidHom.id`, adjunction trivial via
`HolomorphicOneForm.pullback_id`).

Sister to `PeriodPairingMorphism.id'_ofSmoothCycle` (which is the
`ofSmoothCycle`-specialised variant) and to `PeriodPairingMorphism.comp`
(general composition).
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Identity period-pairing morphism.** For any `data : PeriodPairingData X`,
the identity curve map gives the identity cycle pushforward, with
adjunction reducing to `HolomorphicOneForm.pullback_id`. -/
noncomputable def PeriodPairingMorphism.id
    (data : PeriodPairingData X) :
    PeriodPairingMorphism data data where
  f := _root_.id
  contMDiff_f := contMDiff_id
  cyclePush := AddMonoidHom.id data.H1
  adjunction := by
    intro γ τ
    show data.pairing γ τ
      = data.pairing γ (HolomorphicOneForm.pullback _root_.id contMDiff_id τ)
    rw [HolomorphicOneForm.pullback_id]

@[simp] theorem PeriodPairingMorphism.id_f
    (data : PeriodPairingData X) :
    (PeriodPairingMorphism.id data).f = _root_.id := rfl

@[simp] theorem PeriodPairingMorphism.id_cyclePush
    (data : PeriodPairingData X) :
    (PeriodPairingMorphism.id data).cyclePush = AddMonoidHom.id data.H1 := rfl

end JacobianChallenge

end
