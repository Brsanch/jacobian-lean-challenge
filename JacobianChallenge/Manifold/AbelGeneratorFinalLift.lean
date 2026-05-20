/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorPrincipalDivisorZero
import JacobianChallenge.Manifold.PrincipalDivisorOfConstantMap

set_option linter.unusedSectionVars false

/-! # Final two-hypothesis universal lift of the AbelGenerator claim

Composes
`abelGeneratorPeriodCondition_of_period_and_constant_divisor_zero`
with the in-tree bridge
`principalDivisorMap_eq_zero_of_isConstantMap`, eliminating the
`h_constant_divisor_zero` argument entirely. The result reduces
`AbelGeneratorPeriodCondition B` to exactly **two** named
hypotheses:

* `h_period` — the substantive residual content (step 9 proper:
  the regularLevelSetChain's period vector is in the period lattice
  for every non-constant `f` with regular endpoints `(0, ∞)`).

* `h_endpoints` — endpoint regularity (every non-constant `f` has
  `0`, `∞` ∈ `regularValueSet f`; expected dischargeable from
  `criticalValues_finite` + classical density / Möbius reduction).

The constant-case discharge is fully internal via the in-tree
infrastructure.

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

/-- **Final two-hypothesis universal lift.**

`AbelGeneratorPeriodCondition B` follows from exactly two named
hypotheses:

1. `h_period` — period-in-lattice claim for the concrete
   `regularLevelSetChain f` at every non-constant `f` with regular
   endpoints `(0, ∞)`. This is the genuine substantive residual
   content of step 9 of the C3 sub-arc (the Stokes/residue argument
   for the lattice clause).

2. `h_endpoints` — every non-constant `f` has `0` and `∞` as regular
   values. (Classically: `criticalValues f` is finite, so the
   complement is open dense in `RS`; a generic Möbius pre-composition
   arranges this.)

The constant-case discharge is mechanical and discharged internally
via `principalDivisorMap_eq_zero_of_isConstantMap` composed with
`abelGeneratorPeriodConditionAt_of_principalDivisor_zero`. -/
theorem abelGeneratorPeriodCondition_of_period_and_endpoints
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
        (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B :=
  abelGeneratorPeriodCondition_of_period_and_constant_divisor_zero (B := B)
    h_period h_endpoints
    (fun f hc => f.principalDivisorMap_eq_zero_of_isConstantMap hc)

end MeromorphicNonzero

end JacobianChallenge

end
