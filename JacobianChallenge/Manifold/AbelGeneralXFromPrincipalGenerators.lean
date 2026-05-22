/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneralXHypotheses
import JacobianChallenge.Manifold.AbelHypothesisFromPrincipal

set_option linter.unusedSectionVars false

/-! # `AbelGeneralXHypothesis` from the principal-generator statement (Frontier-1)

Refines Phase E's `AbelGeneralXHypothesis X` to its **atomic
generator-only form**: vanishing of `B.abelJacobiDivHom` on the
*principal-divisor generators* `principalDivisorMap f` for each
`f : MeromorphicNonzero X`. This is the genuine atomic content of
Abel's theorem on a compact Riemann surface — vanishing on the full
`Div⁰` subgroup follows by additivity (`AddSubgroup.closure_induction`)
via the existing in-tree lemma
`AbelJacobiInputSymp.abelHypothesis_of_abelJacobiDivHom_principal_zero`
(`Manifold/AbelHypothesisFromPrincipal.lean` line 52).

## What this file ships

* `PrincipalDivisorAJVanishingHypothesis X` — the atomic generator-only
  Prop: for every `(α, h, B)` on X and every `f : MeromorphicNonzero X`,
  `B.abelJacobiDivHom (principalDivisorMap f) = 0`.

* `abelGeneralXHypothesis_of_principalDivisorAJVanishing` — bridge:
  the generator-only statement implies `AbelGeneralXHypothesis X`
  unconditionally via the existing `closure_induction` lifting.

## Why this matters

`AbelGeneralXHypothesis X` quantifies over **all** of `Div⁰ X` (an
infinite-dimensional set), making it hard to discharge directly. The
refinement quantifies only over `MeromorphicNonzero X` and the
generator map — a much more concrete classical statement matching
the form of Abel's theorem in classical references ("the divisor of
a meromorphic function has trivial Abel-Jacobi image"). The bridge
to the closure form is purely algebraic.

Combined with future chips:
* The residue theorem `ResidueTheorem X` (in tree as a named Prop in
  `Divisor/PrincipalDivisorRange.lean`, with an in-tree assembly bundle
  `SumOfResiduesPartitionOfUnity_hypothesis`).
* A bridge from `ResidueTheorem` to `PrincipalDivisorAJVanishingHypothesis`
  (via integrating against holomorphic 1-forms and Stokes on level-set
  2-chains).

→ `AbelGeneralXHypothesis X` becomes a corollary of the residue theorem
plus chip D's `holomorphicStokesHypothesis_holds_unconditional`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Atomic generator-only form of Phase E.** Vanishing of
`B.abelJacobiDivHom` on the *principal-divisor generators*
`principalDivisorMap f` for each `f : MeromorphicNonzero X`,
quantified over all `(α, h, B)`.

This is the classical Abel theorem stripped of `AddSubgroup`-closure
bookkeeping. -/
def PrincipalDivisorAJVanishingHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInputSymp α h)
    (f : MeromorphicNonzero X),
    B.abelJacobiDivHom (principalDivisorMap f) = 0

/-- **Bridge: principal-generator vanishing ⇒ `AbelGeneralXHypothesis`.**
Lifts the atomic generator-only statement to the full `Div⁰`-subgroup
form via `AbelJacobiInputSymp.abelHypothesis_of_abelJacobiDivHom_principal_zero`. -/
theorem abelGeneralXHypothesis_of_principalDivisorAJVanishing
    (h_gen : PrincipalDivisorAJVanishingHypothesis X) :
    AbelGeneralXHypothesis X := by
  intro α h_symp B
  exact AbelJacobiInputSymp.abelHypothesis_of_abelJacobiDivHom_principal_zero
    B (h_gen α h_symp B)

end JacobianChallenge

end
