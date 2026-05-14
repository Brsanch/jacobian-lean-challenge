/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The "discharged" set of generators for `AbelGeneratorPeriodCondition`

For a fixed `B : AbelJacobiInput α h`, define

  `dischargedGenerators B :=
     { f : MeromorphicNonzero X |
        complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α }`

i.e. the set of meromorphic functions for which the period-vector
condition holds.  By construction,

  `AbelGeneratorPeriodCondition B ↔ dischargedGenerators B = Set.univ`.

The point of this file is to show that `dischargedGenerators B` is
*algebraically closed*: it contains `1`, every non-zero constant, and
is closed under multiplication.  Closure follows from

* `principalDivisorMap_mul` (`Divisor/PrincipalDivisor.lean`):
  `principalDivisorMap (f * g) = principalDivisorMap f + principalDivisorMap g`.
* `principalDivisorAJChain_add` (`AbelHypothesisFromPeriodCondition.lean`):
  the AJ-chain is additive in the divisor.
* `complexChainPeriodVector_principalDivisorAJChain_add_mem` (same file):
  the lattice membership is closed under addition.

The substantive C3 work that remains is exhibiting `dischargedGenerators
B = Set.univ` — i.e. discharging the period-vector condition on every
meromorphic function.  Classically this is Abel forward via the
level-set chain Stokes argument.  The algebra-structure layer in this
file lets that discharge proceed on a *multiplicative generating set*
of `MeromorphicNonzero X` rather than every function individually.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Discharged-generators set.** Meromorphic functions whose
principal-divisor AJ-chain has period vector in `periodLatticeImage`.
This is the per-generator atomic content of
`AbelGeneratorPeriodCondition`. -/
def dischargedGenerators (B : AbelJacobiInput α h) : Set (MeromorphicNonzero X) :=
  { f | complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α }

lemma mem_dischargedGenerators_iff (B : AbelJacobiInput α h)
    (f : MeromorphicNonzero X) :
    f ∈ B.dischargedGenerators ↔
      complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := Iff.rfl

/-- **Vacuous discharge by zero principal divisor.** Any `f` with
`principalDivisorMap f = 0` is in `dischargedGenerators`. The AJ chain
of the zero divisor is `0`, whose period vector is `0`, which lies in
every subgroup. -/
theorem mem_dischargedGenerators_of_principalDivisor_zero
    (B : AbelJacobiInput α h) {f : MeromorphicNonzero X}
    (hf : principalDivisorMap f = 0) :
    f ∈ B.dischargedGenerators := by
  show complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap f))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
  rw [hf, B.principalDivisorAJChain_zero,
      complexChainPeriodVector_zero α]
  exact zero_mem _

/-- **Unit is discharged.** `principalDivisorMap_one` gives
`principalDivisorMap 1 = 0`, then the zero-divisor lemma applies. -/
theorem one_mem_dischargedGenerators (B : AbelJacobiInput α h) :
    (1 : MeromorphicNonzero X) ∈ B.dischargedGenerators :=
  B.mem_dischargedGenerators_of_principalDivisor_zero principalDivisorMap_one

/-- **Constants are discharged.** `principalDivisorMap_const` gives
`principalDivisorMap (const c hc) = 0`. -/
theorem const_mem_dischargedGenerators (B : AbelJacobiInput α h)
    (c : ℂ) (hc : c ≠ 0) :
    MeromorphicNonzero.const (X := X) c hc ∈ B.dischargedGenerators :=
  B.mem_dischargedGenerators_of_principalDivisor_zero (principalDivisorMap_const c hc)

/-- **Multiplicative closure of the discharged set.** Composes
`principalDivisorMap_mul` (additivity of the principal-divisor map on
products) with `complexChainPeriodVector_principalDivisorAJChain_add_mem`
(lattice membership is preserved by chain addition). -/
theorem mul_mem_dischargedGenerators (B : AbelJacobiInput α h)
    {f g : MeromorphicNonzero X}
    (hf : f ∈ B.dischargedGenerators) (hg : g ∈ B.dischargedGenerators) :
    f * g ∈ B.dischargedGenerators := by
  show complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap (f * g)))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
  rw [principalDivisorMap_mul]
  exact complexChainPeriodVector_principalDivisorAJChain_add_mem B hf hg

/-! ## Reduction of `AbelGeneratorPeriodCondition` to the discharged-set form -/

/-- **`AbelGeneratorPeriodCondition` ↔ universal discharge.** The
named-hypothesis content is exactly: every `f : MeromorphicNonzero X`
lies in `dischargedGenerators B`. -/
theorem abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ
    (B : AbelJacobiInput α h) :
    AbelGeneratorPeriodCondition B ↔
      B.dischargedGenerators = (Set.univ : Set (MeromorphicNonzero X)) := by
  refine ⟨fun hCond => Set.eq_univ_of_forall fun f => hCond f, fun hUniv f => ?_⟩
  -- `hUniv : dischargedGenerators B = univ`; deduce membership for every `f`.
  have hmem : f ∈ B.dischargedGenerators := by rw [hUniv]; exact Set.mem_univ f
  exact hmem

/-- **One-step `AbelGeneratorPeriodCondition` from the discharged-set
form.** Unfolds the universally-quantified named hypothesis through
`dischargedGenerators`. -/
theorem abelGeneratorPeriodCondition_of_forall_mem_dischargedGenerators
    (B : AbelJacobiInput α h)
    (h_all : ∀ f : MeromorphicNonzero X, f ∈ B.dischargedGenerators) :
    AbelGeneratorPeriodCondition B := h_all

/-- **`AbelHypothesis` from universal discharge.** Composes
`abelGeneratorPeriodCondition_of_forall_mem_dischargedGenerators` with
the per-generator chain reduction
`abelHypothesis_of_abelGeneratorPeriodCondition`. -/
theorem abelHypothesis_of_forall_mem_dischargedGenerators
    (B : AbelJacobiInput α h)
    (h_all : ∀ f : MeromorphicNonzero X, f ∈ B.dischargedGenerators) :
    AbelHypothesis B :=
  abelHypothesis_of_abelGeneratorPeriodCondition B
    (B.abelGeneratorPeriodCondition_of_forall_mem_dischargedGenerators h_all)

end AbelJacobiInput

end JacobianChallenge

end
