/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option linter.unusedSectionVars false

/-! # `PrincDiv X` membership → witness `MeromorphicNonzero` function

The honest `PrincDiv X = PrincDivHonestCandidateGerm X = range principalDivisorAddHom`
(`Divisor/PrincipalDivisorRange.lean`). For any `D ∈ PrincDiv X`, there
exists `f : MeromorphicNonzero X` such that `principalDivisorMap f = D`.

This is the **witness extraction** lemma: it says principal divisors are
"single-function" — every element of `PrincDiv X` is the principal
divisor of *one* `MeromorphicNonzero` function (not just a finite
ℤ-combination), because `MeromorphicNonzero.Germ X` carries a `CommGroup`
structure so the range of the additive hom is genuinely an `AddSubgroup`
(equivalently, the addition / negation operations on `Div X` lift to
multiplication / inverse on `MeromorphicNonzero.Germ X`).

This chip is the **first step** in attacking item 16 (`ofCurve_inj`):
under `0 < genus X`, if `[δ Q₁ - δ P] = [δ Q₂ - δ P]` in `Pic⁰ X`, then
`single Q₁ - single Q₂ ∈ PrincDiv X`, and this lemma extracts the
witness meromorphic function with that specific divisor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Witness extraction from `PrincDiv` membership.** Every element of
`PrincDiv X` is the principal divisor `principalDivisorMap f` of some
single meromorphic function `f : MeromorphicNonzero X`.

The proof unfolds `PrincDiv X = PrincDivHonestCandidate X` and uses
`PrincDivHonestCandidateGerm_eq` to switch to the germ-based range form,
which (since `MeromorphicNonzero.Germ X` is a `CommGroup`) is genuinely
the range of an `AddMonoidHom` — so every element is the image of a
single germ, and any germ representative gives a witness function. -/
theorem exists_meromorphicNonzero_principalDivisorMap_of_mem_PrincDiv
    {D : Div X} (hD : D ∈ PrincDiv X) :
    ∃ f : MeromorphicNonzero X, principalDivisorMap f = D := by
  -- Step 1: `PrincDiv X = PrincDivHonestCandidate X` (definitional in the source
  -- file) and `PrincDivHonestCandidate X = PrincDivHonestCandidateGerm X`
  -- as subgroups (`PrincDivHonestCandidateGerm_eq`).
  have hD_germ : D ∈ PrincDivHonestCandidateGerm X := by
    rw [PrincDivHonestCandidateGerm_eq]
    -- `PrincDivHonestCandidate X = PrincDiv X` by definition. Don't rewrite
    -- since `PrincDiv` unfolds via `noncomputable def`; just use the
    -- definitional equality directly.
    show D ∈ PrincDivHonestCandidate X
    exact hD
  -- Step 2: `PrincDivHonestCandidateGerm = range principalDivisorAddHom`
  -- (definitional). Extract a germ witness.
  unfold PrincDivHonestCandidateGerm at hD_germ
  obtain ⟨g, hg⟩ := hD_germ
  -- `g : Additive (MeromorphicNonzero.Germ X)`,
  -- `principalDivisorAddHom g = D`.
  -- The map `principalDivisorAddHom g` definitionally unfolds to
  -- `MeromorphicNonzero.Germ.principalDivisorMap (Additive.toMul g)`.
  -- Use `Quotient.inductionOn` on `Additive.toMul g` to get a representative.
  -- We carry `hg` as the rewrite target.
  have hg' : MeromorphicNonzero.Germ.principalDivisorMap (Additive.toMul g) = D := hg
  -- Now induct directly on the underlying germ.
  induction h_eq : Additive.toMul g using Quotient.inductionOn with
  | _ f =>
    refine ⟨f, ?_⟩
    -- Rewrite using h_eq:
    rw [← MeromorphicNonzero.Germ.principalDivisorMap_mk f]
    -- Goal: `MeromorphicNonzero.Germ.principalDivisorMap (Germ.mk f) = D`.
    -- We have `Additive.toMul g = Germ.mk f` (from h_eq, after the induction
    -- the binder gives `Quotient.mk _ f = Germ.mk f` definitionally).
    rw [show (MeromorphicNonzero.Germ.mk f) = Additive.toMul g from h_eq.symm]
    exact hg'

end JacobianChallenge

end
