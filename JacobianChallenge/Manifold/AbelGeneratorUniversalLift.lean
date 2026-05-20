/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorAtRegularEndpoints

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Universal lift of the per-`f` AbelGenerator reduction

Lifts `abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period`
(per-`f` claim) to a universal `AbelGeneratorPeriodCondition B` claim,
under three named hypotheses:

* `h_period` — universal period-in-lattice claim for the concrete
  `regularLevelSetChain f` (the residual content of step 9 proper).
* `h_endpoints` — every non-constant `f` has `0` and `∞` as regular
  values (classical content: `regularValueSet f` is cofinite in `RS`).
* `h_constant` — for constant `f`, the AJ chain's period is in the
  lattice (trivial: `principalDivisorMap f = 0` so the AJ chain is
  `0`, period `0`).

The chip case-splits on `IsConstantMap f.toRiemannSphere`: the
non-constant branch invokes the per-`f` reduction with the
endpoint regularity from `h_endpoints`; the constant branch
discharges via `h_constant`. Each branch's hypothesis remains
factored out so the chip is **mechanical** and forwards the
substantive content unchanged.

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

/-- **Universal AbelGenerator from per-`f` regular-endpoint period
claim + endpoint regularity + constant discharge.**

Discharges `AbelGeneratorPeriodCondition B` from three modular
hypotheses, one per case of `IsConstantMap f.toRiemannSphere`:

1. **Non-constant branch.** For every non-constant `f` with `0`,`∞`
   regular values, the concrete `regularLevelSetChain f`'s period
   vector is in `periodLatticeImage`. (Residual classical content of
   step 9.)

2. **Endpoint regularity.** Every non-constant `f` has `0` and `∞`
   regular. (Holds when the construction of `f` arranges this;
   classically, every non-constant `f` can be replaced by a
   precomposed Möbius copy whose `0`,`∞` are regular.)

3. **Constant branch.** For every constant `f` (in the sense of
   `IsConstantMap f.toRiemannSphere`), the AJ chain's period is in
   the lattice. (Trivial when `principalDivisorMap f = 0`; e.g.,
   for `MeromorphicNonzero.const c hc` via
   `principalDivisorMap_const`.) -/
theorem abelGeneratorPeriodCondition_of_universal_inputs
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
    (h_constant : ∀ (f : MeromorphicNonzero X),
        JacobianChallenge.IsConstantMap f.toRiemannSphere →
        complexChainPeriodVector α
            (B.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α) :
    JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B := by
  intro f
  by_cases hc : JacobianChallenge.IsConstantMap f.toRiemannSphere
  · exact h_constant f hc
  · obtain ⟨h0_reg, h_inf_reg⟩ := h_endpoints f hc
    exact abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period
      B f hc h0_reg h_inf_reg (h_period f hc h0_reg h_inf_reg)

end MeromorphicNonzero

end JacobianChallenge

end
