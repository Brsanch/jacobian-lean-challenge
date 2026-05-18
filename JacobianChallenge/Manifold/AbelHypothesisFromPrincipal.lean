/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputSymp
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option linter.unusedSectionVars false

/-! # `AbelHypothesis` from "Abel-on-principals"

`AbelHypothesisSymp B` states that the Abel-Jacobi map vanishes on
**all** elements of `PrincDiv X = AddSubgroup.closure (range principalDivisorMap)`
(when read as a subgroup of `Div0 X`). Classically, Abel's theorem only
gives vanishing on the *generators* — principal divisors `(f)` for
`f : MeromorphicNonzero X` — and the full subgroup follows by
`AddSubgroup.closure_induction` together with additivity of
`abelJacobiDivHom`.

This file factors `AbelHypothesisSymp` through the generator-only
named input `abelJacobiDivHom (principalDivisorMap f) = 0` — i.e.
**Abel's theorem itself** stripped of the subgroup-closure
bookkeeping. Downstream consumers can supply the generator-only
classical content and obtain the full `AbelHypothesisSymp`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace AbelJacobiInputSymp

universe u

/-- **`AbelHypothesis` reduces to vanishing on principal-divisor generators.**

For any `B : AbelJacobiInputSymp α h`, the full
`AbelHypothesis B` (Abel's theorem in subgroup form) is equivalent to
the generator-only statement `∀ f, B.abelJacobiDivHom (principalDivisorMap f) = 0`.

This forward direction uses `AddSubgroup.closure_induction` to lift
vanishing on generators to vanishing on the full closure, exploiting
that `abelJacobiDivHom : Div X →+ AnalyticJacobianSymp …` is an
`AddMonoidHom` (so already linear in the closure operations of `+`,
`0`, `neg`). The reverse direction is the generator-membership lemma
`principalDivisorMap_mem_PrincDiv`. -/
theorem abelHypothesis_of_abelJacobiDivHom_principal_zero
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}
    (B : AbelJacobiInputSymp α h)
    (h_princ : ∀ f : MeromorphicNonzero X,
        B.abelJacobiDivHom (principalDivisorMap f) = 0) :
    AbelHypothesis B := by
  intro D hD
  -- Unfold `abelJacobiDiv0Hom D = abelJacobiDiv (D : Div X) = abelJacobiDivHom (D : Div X)`.
  rw [abelJacobiDiv0Hom_apply]
  show B.abelJacobiDivHom (D : Div X) = 0
  -- `(D : Div X) ∈ PrincDiv X = AddSubgroup.closure (range principalDivisorMap)`.
  -- Use closure_induction on the underlying AddSubgroup.
  unfold PrincDiv PrincDivHonestCandidate at hD
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hD
  · -- Generator case: x ∈ range principalDivisorMap.
    rintro x ⟨f, rfl⟩
    exact h_princ f
  · -- Zero case.
    exact map_zero _
  · -- Add case.
    intro x y _ _ hx hy
    rw [map_add, hx, hy, zero_add]
  · -- Neg case.
    intro x _ hx
    rw [map_neg, hx, neg_zero]

end AbelJacobiInputSymp

end JacobianChallenge

end
