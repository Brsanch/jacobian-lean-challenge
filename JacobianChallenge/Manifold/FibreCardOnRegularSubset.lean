/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Degree

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Fibre-cardinality well-definedness on the regular subset (ZZ134)

## Goal

ZZ129 introduced the strengthened witness `RegularValueWitnessReg f C`
(see `JacobianChallenge.Manifold.Degree`), which packages a
`RegularValueWitness f` with a regularity certificate `value ∉ C` against
an externally-supplied critical-value set `C : Set Y`.

This file delivers a clean, structurally-trivial discharge of
`fibre_card_well_defined_at_regular_statement`-shape conclusions whose
support set is *literally* the complement `R := Y \ C`. The point: the
`is_regular` field of `RegularValueWitnessReg f C` already says
`value ∉ C`, which is *definitionally* `value ∈ Y \ C`. Hence the
`h_supp` hypothesis of `fibre_card_eq_of_locallyConstant_subtype_reg`
becomes automatic, and no caller needs to thread it.

## What is delivered

* `RegularValueWitnessReg.value_mem_compl` — trivial helper.
* `fibre_card_eq_of_locallyConstant_compl` — drop-in form of
  `fibre_card_eq_of_locallyConstant_subtype_reg` with `R := Cᶜ` and the
  `h_supp` hypothesis discharged from the regularity certificate.
* `fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`
  and the named-`Prop` variant — uniform top-level reductions.

## Status

Purely structural. The two analytic obligations
(`IsLocallyConstant` of `card_of` on `Cᶜ`, `IsPreconnected` of `Cᶜ`) are
inputs — they would be discharged by the analytic implicit-function
theorem on Riemann surfaces (local triviality of regular-value covering)
and the connectedness lemma "connected real-2-manifold minus finite is
connected", neither of which is formalised at this mathlib pin.

This file does **not** discharge those analytic facts. It strips the
trivial `h_supp` plumbing out of any caller that uses
`RegularValueWitnessReg f C` with `R = Cᶜ`, which is the canonical
choice.

No `sorry`. No `axiom`. No signature changes outside this file. -/

@[expose] public section

open Set

namespace JacobianChallenge

namespace ContMDiff

universe u v

/-- **Trivial helper.** A regular witness against critical-value set `C`
has value in `Cᶜ`. -/
lemma RegularValueWitnessReg.value_mem_compl
    {X : Type u} {Y : Type v}
    {f : X → Y} {C : Set Y} (w : RegularValueWitnessReg f C) :
    w.toWitness.value ∈ (Cᶜ : Set Y) :=
  w.is_regular

namespace Owed.degree

/-- **Discharge with `R := Cᶜ`.** Specialisation of
`fibre_card_eq_of_locallyConstant_subtype_reg` to the canonical regular
subset `Cᶜ`. The `h_supp` premise of the general form is automatic from
the regularity certificate built into `RegularValueWitnessReg`, so
callers no longer need to supply it.

Inputs:
* `card_of : Y → ℕ` — fibre-cardinality function on `Y`.
* `h_witness` — `card_of` reads off any plain `RegularValueWitness`'s card.
  (Plain, not regular: `card_of` does not depend on the certificate.)
* `h_lc_sub` — `card_of` is locally constant on the subtype `Cᶜ`.
  This is the analytic / covering-space content (local triviality).
* `h_conn_sub` — the subtype `Cᶜ` is preconnected. This is the
  topological content (connected surface minus finite is preconnected).

Conclusion: any two regular witnesses against `C` give the same fibre
cardinality. -/
lemma fibre_card_eq_of_locallyConstant_compl
    {X : Type u} {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} {C : Set Y}
    (card_of : Y → ℕ)
    (h_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card)
    (h_lc_sub : IsLocallyConstant
      (fun y : (Cᶜ : Set Y) => card_of y.val))
    (h_conn_sub : IsPreconnected (Set.univ : Set (Cᶜ : Set Y)))
    (w₁ w₂ : RegularValueWitnessReg f C) :
    w₁.card = w₂.card :=
  fibre_card_eq_of_locallyConstant_subtype_reg
    (R := (Cᶜ : Set Y)) card_of h_witness
    (fun w => w.value_mem_compl) h_lc_sub h_conn_sub w₁ w₂

/-! ## Top-level reduction (uniform over `f`) -/

/-- **Top-level reduction (regular-form).** The
`fibre_card_well_defined_at_regular_statement`-shape conclusion for a
*specific* critical-value set `C : Set Y` follows from the existence,
for every non-constant analytic `f`, of a fibre-cardinality function
that is locally constant on the canonical regular subset `Cᶜ`, together
with preconnectedness of `Cᶜ`.

This packages `fibre_card_eq_of_locallyConstant_compl` into the
quantified shape consumed by `fibre_card_well_defined_at_regular_statement`,
discharging everything except the two analytic inputs. -/
lemma fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y),
        ∃ (card_of : Y → ℕ),
          (∀ w : RegularValueWitness f, card_of w.value = w.card) ∧
          IsLocallyConstant (fun y : (Cᶜ : Set Y) => card_of y.val) ∧
          IsPreconnected (Set.univ : Set (Cᶜ : Set Y))) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y) (w₁ w₂ : RegularValueWitnessReg f C), w₁.card = w₂.card := by
  intro f hf hnc C w₁ w₂
  obtain ⟨card_of, h_witness, h_lc_sub, h_conn_sub⟩ := h_lc f hf hnc C
  exact fibre_card_eq_of_locallyConstant_compl
    card_of h_witness h_lc_sub h_conn_sub w₁ w₂

/-- **Top-level reduction (regular-form), `Owed.degree.fibre_card_well_defined_at_regular_statement`
shape.** Same as `fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`,
but stated via the named `Prop` for downstream callers. -/
lemma fibre_card_well_defined_at_regular_statement_holds_of_locallyConstant
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y),
        ∃ (card_of : Y → ℕ),
          (∀ w : RegularValueWitness f, card_of w.value = w.card) ∧
          IsLocallyConstant (fun y : (Cᶜ : Set Y) => card_of y.val) ∧
          IsPreconnected (Set.univ : Set (Cᶜ : Set Y))) :
    fibre_card_well_defined_at_regular_statement X Y :=
  fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant
    (X := X) (Y := Y) h_lc

end Owed.degree

end ContMDiff

end JacobianChallenge
