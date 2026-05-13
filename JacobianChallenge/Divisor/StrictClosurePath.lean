/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Manifold.ResidueTheorem

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Strict-closure path: from R5 to honest items 15/19/20

This file is a **wiring receipt**. It glues real existing lemmas to make
the strict-closure chain mechanically explicit in one place.

## Status (2026-05-13)

The full chain is now closed. R5 is discharged unconditionally by
`Manifold/R5Unconditional.R5_principal_degree_zero_statement_holds`, and
`PrincDiv X := PrincDivHonestCandidate X` is the active definition in
`Divisor/PrincipalDivisorRange.lean` (post-ZZ256). Items 15, 19, 20 in
`Basic.lean` are STRICT-CLOSED.

## The chain visually

```
  R5 (residue theorem on compact RS)
    — discharged: R5Unconditional.R5_principal_degree_zero_statement_holds
    ↓ [residueTheorem_iff_range_le_Div0]
  PrincDivHonestCandidate X ⊆ Div0 X
    ↓ [PrincDiv := PrincDivHonestCandidate in PrincipalDivisorRange.lean]
  Honest PrincDiv X
    ↓ [Pic0 X = Div0 X / (PrincDiv X).addSubgroupOf is the analytic Jacobian]
  Items 15, 19, 20 — STRICT-CLOSED.
```

## What lives where

* `R5_principal_degree_zero_statement X` (named statement) is declared in
  `Manifold/ResidueTheorem.lean`. Its discharge is
  `R5_principal_degree_zero_statement_holds` in
  `Manifold/R5Unconditional.lean`, composing in-tree R4 with
  `residue_theorem_of_R4`.

* The equivalence `ResidueTheorem X ↔ PrincDivHonestCandidate X ≤ Div0 X`
  is `residueTheorem_iff_range_le_Div0`, proved (no `sorry`, no `Iff.rfl`)
  in `Divisor/PrincipalDivisorRange.lean`.

* The `PrincDiv := PrincDivHonestCandidate` swap is performed in
  `Divisor/PrincipalDivisorRange.lean:437` (ZZ256). The honest `PrincDiv X`
  references `principalDivisorMap`, which would import-cycle through
  `Divisor.lean`, so the active definition lives in
  `PrincipalDivisorRange.lean` rather than `Divisor.lean`.

## What this file does

* Provides `PrincDivHonestCandidate_le_Div0_of_R5` (conditional on the R5
  hypothesis) and the alias `PrincDivHonestCandidate_le_Div0_of_trigger`.
  R5 is now in-tree unconditional, so these conditional forms compose
  cleanly with `R5_principal_degree_zero_statement_holds` to give an
  unconditional `PrincDivHonestCandidate ≤ Div0` whenever needed.
* Introduces **no axioms** and uses **no `sorry`**.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The strict-closure path: R5 ⇒ honest principal divisors land in `Div0`.**

Combines:
- `ResidueTheorem.R5_principal_degree_zero_statement` (in
  `Manifold/ResidueTheorem.lean`, the named R5 owed statement),
- with the `↔` in `Divisor/PrincipalDivisorRange.lean`'s
  `residueTheorem_iff_range_le_Div0`,

yielding: if R5 holds (in the form of
`ResidueTheorem.R5_principal_degree_zero_statement X`, equivalently
`ResidueTheorem X`), then `PrincDivHonestCandidate X ≤ Div0 X`.

The hypothesis `hR5` is taken in its unfolded `∀ f, … = 0` form so that
this lemma matches both the `R5_principal_degree_zero_statement` shape and
the `ResidueTheorem` shape (both are definitionally this `∀`-statement). -/
theorem PrincDivHonestCandidate_le_Div0_of_R5
    (hR5 : ∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0) :
    PrincDivHonestCandidate X ≤ Div0 X :=
  (residueTheorem_iff_range_le_Div0 (X := X)).mp hR5

/-- **The strict-closure trigger:** if R5 is discharged, the eventual honest
`PrincDiv X` is `PrincDivHonestCandidate X` (rather than the placeholder
`⊥`), and items 15, 19, 20 in `Basic.lean` strict-close on the spot.

This `def` does **not** discharge R5 — that is the deep classical input.
What this file gives is the receipt that everything *downstream* of R5 is
mechanically wired. -/
def StrictClosureTrigger (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  ∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0

/-- The strict-closure trigger statement is exactly the residue theorem
(and is exactly the `R5_principal_degree_zero_statement` shape from
`Manifold/ResidueTheorem.lean`).

This is `Iff.rfl` because `StrictClosureTrigger X`, `ResidueTheorem X`, and
`ResidueTheorem.R5_principal_degree_zero_statement X` all unfold to the
same `∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`. -/
lemma strictClosureTrigger_iff_residueTheorem :
    StrictClosureTrigger X ↔ ResidueTheorem X :=
  Iff.rfl

/-- The strict-closure trigger is also definitionally `R5`. Provided for
auditability: the reader can see in one step that "trigger = R5 = residue
theorem". -/
lemma strictClosureTrigger_iff_R5 :
    StrictClosureTrigger X ↔ ResidueTheorem.R5_principal_degree_zero_statement X :=
  Iff.rfl

/-- **End-to-end packaging.** Discharging the strict-closure trigger
implies the honest principal-divisor subgroup is contained in the
degree-zero subgroup. This is the receipt that consumers (a future swap of
`PrincDiv` in `Divisor.lean`) need: once R5 / `StrictClosureTrigger X` is
in hand, `Pic0 X = Div0 X / (PrincDiv X).addSubgroupOf (Div0 X)` becomes
the genuine analytic Picard group, and items 15, 19, 20 strict-close. -/
theorem PrincDivHonestCandidate_le_Div0_of_trigger
    (hTrigger : StrictClosureTrigger X) :
    PrincDivHonestCandidate X ≤ Div0 X :=
  PrincDivHonestCandidate_le_Div0_of_R5 hTrigger

end JacobianChallenge

end
