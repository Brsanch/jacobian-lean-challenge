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

This file is a pure **wiring receipt**. It introduces no new mathematical
content; it just makes the strict-closure chain mechanically explicit so a
strict reader can see the whole route in one place. Every arrow below is a
*real existing lemma/def in the repo* — the file just glues them.

## The chain visually

```
StrictClosurePath chain:

  R5 (residue theorem on compact RS)
    ↓ [residueTheorem_iff_range_le_Div0]
  PrincDivHonestCandidate X ⊆ Div0 X
    ↓ [one-line edit in Divisor.lean: PrincDiv := PrincDivHonestCandidate]
  Honest PrincDiv X (no longer ⊥)
    ↓ [Pic0 X = Div0 X / (PrincDiv X).addSubgroupOf becomes meaningful]
  Items 15, 19, 20 (PROOF-HONEST today) strict-close.
    - ofCurve_self [δP - δP = 0 in honest Pic⁰] ✓
    - pushforward_id_apply [Div.singletonMap_id functoriality] ✓
    - pushforward_comp_apply [Div.singletonMap_comp functoriality] ✓
```

## What lives where

* The R5 hypothesis is the named owed statement
  `JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement`,
  declared in `Manifold/ResidueTheorem.lean` (the only file in the repo
  where `sorry` is allowed). It is the bottom-line input to the
  topological-degree Route A breakdown documented in that file.

* The equivalence `ResidueTheorem X ↔ PrincDivHonestCandidate X ≤ Div0 X`
  is `residueTheorem_iff_range_le_Div0`, proved (no `sorry`, no `Iff.rfl`)
  in `Divisor/PrincipalDivisorRange.lean` by routing through
  `AddSubgroup.closure_le`, `AddMonoidHom.mem_ker`, and
  `Div.degreeHom_apply`.

* The eventual one-line swap in `Divisor.lean`,
  ```
  noncomputable def PrincDiv (X : Type*) [...] : AddSubgroup (Div X) :=
    PrincDivHonestCandidate X
  ```
  is **not** performed here — that change is intentionally kept as a single
  one-line edit in `Divisor.lean` so that the move from placeholder `⊥` to
  honest principal-divisor subgroup is auditable in one diff.

* Items 15, 19, 20 in `Basic.lean` are already labelled
  `STUB *(PROOF-HONEST)*` in `OPEN.md`: their proof bodies (in `Jacobian.lean`
  and `Basic.lean`) route through the `Pic0` quotient *abstractly* via
  `Div.singletonMap_id`, `Div.singletonMap_comp`, and `δP − δP = 0`. Those
  arguments survive any honest replacement of `PrincDiv X`. Once the swap
  above happens, the three items become STRICT-CLOSED on the spot — no
  proof-body changes required.

## What this file does *not* do

* It does **not** discharge R5. R5 is the deep classical input (residue
  theorem on a compact connected Riemann surface), owed from
  `Manifold/ResidueTheorem.lean`'s Route A (R1+R2+R3+R4) or the alternative
  Stokes-route sketched in that file's tail. R5 is consumed here as a
  hypothesis only.
* It does **not** modify `JacobianChallenge/Basic.lean`,
  `JacobianChallenge/Manifold/ResidueTheorem.lean`, or
  `JacobianChallenge/Divisor.lean`. The first is the challenge spec
  (untouched by contract), the second already houses its allowed `sorry`
  for R5, and the third stays in placeholder form so the eventual swap is
  a clean one-line audit.
* It introduces **no axioms** and uses **no `sorry`**.
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
