/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorUniversalLift
import JacobianChallenge.Manifold.AbelGeneratorDischargedSet

set_option linter.unusedSectionVars false

/-! # Trivial-divisor discharge of the per-`f` AbelGenerator claim

When `principalDivisorMap f = 0`, the per-`f` AbelGenerator claim
discharges trivially via `B.principalDivisorAJChain_zero`: the AJ
chain is `0`, its period vector is `0`, and `0` is in every
subgroup.

This file ships:

* `abelGeneratorPeriodConditionAt_of_principalDivisor_zero` — direct
  discharge of the per-`f` AbelGenerator claim from
  `principalDivisorMap f = 0`.

* `abelGeneratorPeriodCondition_of_period_at_regular_endpoints_and_constant_divisor_zero`
  — composes `abelGeneratorPeriodCondition_of_universal_inputs` with
  the trivial-divisor discharge: takes `h_period`, `h_endpoints`, and
  `h_constant_divisor_zero` (which says every `IsConstantMap` `f` has
  `principalDivisorMap f = 0`) to yield
  `AbelGeneratorPeriodCondition B`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Module
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [PreconnectedSpace X] [Nonempty X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
variable {h : PeriodLatticeDiscretenessBundle
  (PeriodPairingData.ofSmoothCycle X) α}

/-- **Trivial-divisor discharge of the per-`f` AbelGenerator claim.**
If `principalDivisorMap f = 0`, the AJ chain of the zero divisor is
`0`, whose period vector is `0`, which is in every subgroup. -/
theorem abelGeneratorPeriodConditionAt_of_principalDivisor_zero
    (B : JacobianChallenge.AbelJacobiInput α h)
    (f : MeromorphicNonzero X)
    (hf : principalDivisorMap f = 0) :
    complexChainPeriodVector α
        (B.principalDivisorAJChain (principalDivisorMap f))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  rw [hf, B.principalDivisorAJChain_zero, complexChainPeriodVector_zero α]
  exact zero_mem _

/-- **Universal AbelGenerator from per-`f` period at regular endpoints +
endpoint regularity + (`IsConstantMap → principalDivisorMap = 0`).**

A cleaner restatement of
`abelGeneratorPeriodCondition_of_universal_inputs`: the constant-case
hypothesis is factored through the standard "constant ⇒ trivial
divisor" content, leaving only the named bridge
`h_constant_divisor_zero` plus the substantive `h_period`. -/
theorem abelGeneratorPeriodCondition_of_period_and_constant_divisor_zero
    (B : JacobianChallenge.AbelJacobiInput α h)
    (h_period : ∀ (f : MeromorphicNonzero X)
        (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
        (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
        (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet),
        complexChainPeriodVector α
            (f.regularLevelSetChain hnc h0_reg h_inf_reg)
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α)
    (h_endpoints : ∀ (f : MeromorphicNonzero X),
        ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere →
        (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet ∧
        (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (h_constant_divisor_zero : ∀ (f : MeromorphicNonzero X),
        JacobianChallenge.IsConstantMap f.toRiemannSphere →
        principalDivisorMap f = 0) :
    JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B :=
  abelGeneratorPeriodCondition_of_universal_inputs (B := B)
    h_period h_endpoints
    (fun f hc =>
      abelGeneratorPeriodConditionAt_of_principalDivisor_zero
        B f (h_constant_divisor_zero f hc))

end MeromorphicNonzero

end JacobianChallenge

end
