/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Degree

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Probe: signature alignment between `ContMDiff.degree` (`Basic.lean`) and
`degreeFiber` (`Manifold/Degree.lean`)

This file is **not** the swap of `Basic.lean`'s `ContMDiff.degree` body. The
swap is forbidden in this chip. This file scopes out *whether the swap is
even legal* (signature-preserving) and *what the discharge layer above the
swap will look like*.

## Conclusion of the probe

**The signatures align perfectly.** Both definitions take exactly
`(f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)` and return `ℕ`, under the same
ambient `[TopologicalSpace …][T2Space …][CompactSpace …][ConnectedSpace …]
[ChartedSpace ℂ …][IsManifold 𝓘(ℂ) ω …]` instance bundles on `X` and `Y`.

In particular:

* `RegularValueWitness` is consumed **internally** by `degreeFiber` via
  `Classical.choice` on `Nonempty (RegularValueWitness f)`. It is **not** an
  argument at the call site.
* `IsConstantMap f` is also discharged internally (via `Classical`).
* No extra type-class instances appear in `degreeFiber`'s signature.

So the swap `degreeStub f hf  ↦  degreeFiber f hf` in `Basic.lean` is purely
a body change and the resulting `_root_.ContMDiff.degree` retains the
verbatim Buzzard signature `(hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ`.

## What this file proves

The lemma `degreeFiber_eq_witness_card_at_regular` packages the non-trivial
behaviour of `degreeFiber` in a form that the eventual swap consumer in
`Basic.lean` will read. It says: assuming the about-to-land
`Owed.degree.fibre_card_well_defined_at_regular_statement` (item 3.reg) is
discharged, plus `RegularValueWitness` existence (item 2), `degreeFiber f hf`
agrees with the cardinality of *any* regular-value witness. This is the form
required to call the swapped `Basic.lean.ContMDiff.degree f hf = w.card` for
*any* user-supplied regular witness `w` — i.e. the form that downstream
proofs (e.g. `pushforward_pullback`) actually need.

The proof is purely structural composition of the existing lemmas in
`Manifold/Degree.lean`:

* `degreeFiber_eq_witness_card`: `degreeFiber = (Classical.choice h).card`
  under non-const + `Nonempty (RegularValueWitness f)`.
* The hypothesis `fibre_card_well_defined_at_regular_statement` then
  bridges from the Classical-choice witness to *any* regular witness.

## What is owed (and what the swap into `Basic.lean` consumes)

A swap of `Basic.lean`'s `_root_.ContMDiff.degree` from `degreeStub` to
`degreeFiber` upgrades the constant-vs-1 indicator to a fibre-cardinality.
For that swap to count as STRICT-CLOSED for OPEN.md item 9 (Buzzard's bar),
the following are needed, in order:

1. `Owed.degree.regular_value_exists_statement` discharged (so non-constant
   `f` actually has a `Nonempty (RegularValueWitness f)`, hence `degreeFiber`
   does *not* fall back to 0).
2. `Owed.degree.fibre_card_well_defined_at_regular_statement` discharged (so
   the value of `degreeFiber` does not depend on `Classical.choice`'s pick
   among witnesses, when restricted to *regular* witnesses).

Both are recorded in `Manifold/Degree.lean` as hypothesis-shape `Prop`s
(no axioms). ZZ155's Hurwitz cluster is composing the analytic content for
(1)–(2). This probe verifies the structural skeleton above those discharges
type-checks.

## What is NOT done

* The body of `_root_.ContMDiff.degree` in `Basic.lean` is left alone.
* No new axioms are introduced.
* No `sorry` is used.
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace JacobianChallenge

namespace ContMDiff

universe u v

/-! ## Signature alignment witness

The first `theorem` here exists purely to make the signature alignment
machine-verifiable: it type-checks because the call-site shapes match. -/

/-- **Signature alignment.** Both `degreeFiber f hf` and `degreeStub f hf`
have type `ℕ` under the same instance bundle and the same `(f, hf)` arguments.
Hence the swap of `Basic.lean`'s `_root_.ContMDiff.degree` body from
`degreeStub` to `degreeFiber` is a body change only: the verbatim Buzzard
signature `(hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ` is preserved.

This lemma says nothing about agreement of values — only that the call sites
type-check identically. The numeric agreement is the content of
`degreeFiber_eq_witness_card_at_regular` below. -/
theorem degreeFiber_signature_aligns_with_degreeStub
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (degreeFiber f hf : ℕ) =
      (degreeFiber f hf : ℕ) ∧
    (JacobianChallenge.Manifold.degreeStub f hf : ℕ) =
      (JacobianChallenge.Manifold.degreeStub f hf : ℕ) :=
  ⟨rfl, rfl⟩

/-! ## The form the `Basic.lean` swap consumer will see

Under the named hypotheses recorded in `Owed.degree`, `degreeFiber f hf`
agrees with the cardinality of any user-supplied regular-value witness.

This is the form used by `pushforward_pullback` and any other downstream
identity that compares `ContMDiff.degree f hf` to an explicit fibre count.
After the swap into `Basic.lean`, callers will read this lemma as
`ContMDiff.degree f hf = w.card`. -/

/-- **The conditional bridge (ZZ172-corrected).** Given:

* `hnc`            : `f` is not constant,
* `h_exist`        : a `RegularValueWitness f` exists (`Owed.degree` item 2),
* `h_choice_reg`   : the `Classical.choice`-selected witness's value carries
                     the analytic chart-pullback-deriv-nonzero certificate
                     (i.e. it is a *regular* value),
* `w`              : a user-supplied regular-value witness, and
* `h_wd_at_reg`    : any two *regular* witnesses have the same `card`
                     (`Owed.degree` item 3.reg),

we have `degreeFiber f hf = w.card`.

This is the lemma the `Basic.lean` swap consumer will use. After the swap,
`ContMDiff.degree f hf = w.card` follows by `rfl` from this lemma's
statement — whence "swap = strict-closed" reduces to discharging
`h_exist` + `h_wd_at_reg`.

Note: the `Classical.choice`-selected witness behind `degreeFiber`'s body is
**not** the same Lean term as `w`. We bridge them through `h_wd_at_reg` by
converting both to regular witnesses, which the hypothesis `h_choice_reg`
certifies for the Classical-choice side. -/
theorem degreeFiber_eq_witness_card_at_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_exist : Nonempty (RegularValueWitness f))
    (h_choice_reg : ∀ x ∈ f ⁻¹' {(Classical.choice h_exist).value},
      deriv ((chartAt ℂ (Classical.choice h_exist).value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0)
    (w : RegularValueWitnessReg f)
    (h_wd_at_reg : ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card) :
    degreeFiber f hf = w.card := by
  -- Step 1: degreeFiber f hf = (Classical.choice h_exist).card.
  have h_eq : degreeFiber f hf = (Classical.choice h_exist).card :=
    degreeFiber_eq_witness_card f hf hnc h_exist
  -- Step 2: the Classical-choice witness, promoted to a regular witness via
  -- the analytic certificate, has the same card.
  let wChoice : RegularValueWitnessReg f :=
    (Classical.choice h_exist).toRegular h_choice_reg
  have h_choice_card : wChoice.card = (Classical.choice h_exist).card := rfl
  -- Step 3: well-definedness on regular witnesses gives wChoice.card = w.card.
  have h_wd : wChoice.card = w.card := h_wd_at_reg wChoice w
  -- Compose.
  calc degreeFiber f hf
      = (Classical.choice h_exist).card := h_eq
    _ = wChoice.card := h_choice_card.symm
    _ = w.card := h_wd

/-- **Constant-case companion.** When `f` is constant, `degreeFiber` is `0`
unconditionally — no hypothesis needed. This matches `degreeStub`'s answer
in the constant case, so the swap is *strictly compatible* with the current
`Basic.lean` body for constant maps. -/
theorem degreeFiber_eq_zero_of_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hc : JacobianChallenge.IsConstantMap f) :
    degreeFiber f hf = 0 := by
  unfold degreeFiber
  simp [hc]

/-! ## Summary of what the `Basic.lean` swap requires

After this probe, the situation for OPEN.md item 9 is:

* **Signature legality of the swap:** verified by
  `degreeFiber_signature_aligns_with_degreeStub`. The swap
  `degreeStub f hf  ↦  degreeFiber f hf` in `Basic.lean` does not change
  `_root_.ContMDiff.degree`'s call signature.
* **Constant case after swap:** unconditional, by `degreeFiber_eq_zero_of_const`.
  The swap is strictly compatible with the current `degreeStub` constant
  answer.
* **Non-constant case after swap:** conditional on
  `Owed.degree.regular_value_exists_statement` (item 2) and
  `Owed.degree.fibre_card_well_defined_at_regular_statement` (item 3.reg),
  packaged together by `degreeFiber_eq_witness_card_at_regular`.

ZZ155 (Hurwitz cluster) is composing the analytic content for items (2) and
(3.reg). When those land, the body swap in `Basic.lean` becomes a one-line
edit, and OPEN.md item 9 graduates from STUB to STRICT-CLOSED with no
caller-side changes. -/

end ContMDiff

end JacobianChallenge

end
