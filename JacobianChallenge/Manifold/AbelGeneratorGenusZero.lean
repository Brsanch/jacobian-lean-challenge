/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `AbelGeneratorPeriodCondition` at genus zero

At `genus X = 0`, the period-vector codomain `Fin 0 → ℂ` is a
`Subsingleton`, so every period vector equals `0` definitionally and
trivially lies in `periodLatticeImage α` (the zero element of any
subgroup is the unique element of a subsingleton ambient group).

This closes `AbelGeneratorPeriodCondition B` unconditionally for any
`B : AbelJacobiInput α h` whenever `genus X = 0`.

Related: `AbelHypothesisGenusZero.lean` discharges the upstream
`AbelHypothesis_of_genus_zero` directly via
`Subsingleton (AnalyticJacobian)`. The lemma in this file is the
"atomic" version at the period-vector layer; it composes with the
existing reduction chain `AbelHypothesis ← AbelChainPeriodCondition
← AbelGeneratorPeriodCondition` to give a parallel route at the
sharper, per-generator level.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module Finset

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **`AbelGeneratorPeriodCondition` at genus zero.** When
`genus X = 0`, the period-vector codomain `Fin 0 → ℂ` is a
`Subsingleton` (the unique element is the empty function, equal to
`0`). Hence every period vector lies in `periodLatticeImage α`
trivially. -/
theorem abelGeneratorPeriodCondition_of_genus_zero
    (B : AbelJacobiInput α h)
    (h_genus : JacobianChallenge.genus X = 0) :
    AbelGeneratorPeriodCondition B := by
  intro f
  -- The codomain `Fin (genus X) → ℂ` is a Subsingleton at genus 0.
  -- Any element equals the zero element; in particular the period
  -- vector equals `0`, which lies in any Submodule.
  have h_sub : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    rw [h_genus]
    infer_instance
  rw [Subsingleton.elim
    (complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap f)))
    (0 : Fin (JacobianChallenge.genus X) → ℂ)]
  exact zero_mem _

/-- **`AbelHypothesis` at genus zero via the per-generator route.**
Parallel proof of Abel forward at genus 0 going through
`AbelGeneratorPeriodCondition_of_genus_zero` then
`abelHypothesis_of_abelGeneratorPeriodCondition`. -/
theorem abelHypothesis_of_genus_zero_via_generator
    (B : AbelJacobiInput α h)
    (h_genus : JacobianChallenge.genus X = 0) :
    AbelHypothesis B :=
  abelHypothesis_of_abelGeneratorPeriodCondition B
    (B.abelGeneratorPeriodCondition_of_genus_zero h_genus)

end AbelJacobiInput

end JacobianChallenge

end
