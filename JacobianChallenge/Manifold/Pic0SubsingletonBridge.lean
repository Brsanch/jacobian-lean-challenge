/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Bridge: `Subsingleton (Pic0 X) ↔ every Div0 is principal

`Pic0 X` is defined as the quotient `Div0 X ⧸ (PrincDiv X).addSubgroupOf
(Div0 X)`. A quotient `G ⧸ N` is `Subsingleton` iff `N = ⊤`. Hence
`Subsingleton (Pic0 X)` is equivalent to the statement that the
principal-divisor subgroup-of-`Div0` is everything — i.e., every
degree-zero divisor is principal.

This bridge factors the genus-0 input
`Subsingleton (Pic0 RiemannSphere)` (used in
`Manifold/JacobiInversionGenusZero.lean` and downstream
`AbelJacobiEquivRiemannSphere.lean`) onto an existential statement
over `MeromorphicNonzero X`, which is the form that a future
discharge (constructing explicit meromorphic representatives) will
produce.

## What ships

* `subsingleton_pic0_iff_every_div0_principal` — the bridge as an
  `iff`. Direction `→` uses `Subsingleton.elim` on the zero class;
  direction `←` shows the quotient is trivial.

* `subsingleton_pic0_of_every_div0_principal` — the one-way form
  (the only one likely to be used downstream).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Subsingleton bridge for `Pic0`.** `Subsingleton (Pic0 X)`
holds iff every degree-zero divisor is principal. -/
theorem subsingleton_pic0_iff_every_div0_principal :
    Subsingleton (Pic0 X)
      ↔ ∀ D : Div0 X, (D : Div X) ∈ PrincDiv X := by
  constructor
  · -- Forward: `Subsingleton (Pic0 X)` ⇒ every `Div0` is principal.
    intro hSub D
    -- `(QuotientAddGroup.mk D : Pic0 X) = 0` since codomain is subsingleton.
    have h0 : (QuotientAddGroup.mk D : Pic0 X) = 0 := @Subsingleton.elim _ hSub _ _
    -- The class is zero iff `D ∈ (PrincDiv X).addSubgroupOf (Div0 X)`.
    rw [QuotientAddGroup.eq_zero_iff] at h0
    -- `D ∈ (PrincDiv X).addSubgroupOf (Div0 X)` unfolds to `(D : Div X) ∈ PrincDiv X`.
    exact h0
  · -- Backward: every `Div0` is principal ⇒ `Pic0 X` is subsingleton.
    intro hAllPrinc
    refine ⟨fun x y => ?_⟩
    -- Every class equals `0` since the principal-divisor subgroup is `⊤`.
    induction x using QuotientAddGroup.induction_on with
    | H D₁ =>
      induction y using QuotientAddGroup.induction_on with
      | H D₂ =>
        -- Both `D₁` and `D₂` map to `0` in `Pic0 X`.
        have h1 : (QuotientAddGroup.mk D₁ : Pic0 X) = 0 := by
          rw [QuotientAddGroup.eq_zero_iff]
          exact hAllPrinc D₁
        have h2 : (QuotientAddGroup.mk D₂ : Pic0 X) = 0 := by
          rw [QuotientAddGroup.eq_zero_iff]
          exact hAllPrinc D₂
        rw [h1, h2]

/-- **One-way form** of the bridge — the practical statement for
discharging `Subsingleton (Pic0 X)` from a constructive
"every-Div0-is-principal" hypothesis. -/
theorem subsingleton_pic0_of_every_div0_principal
    (h : ∀ D : Div0 X, (D : Div X) ∈ PrincDiv X) :
    Subsingleton (Pic0 X) :=
  (subsingleton_pic0_iff_every_div0_principal).mpr h

end JacobianChallenge

end
