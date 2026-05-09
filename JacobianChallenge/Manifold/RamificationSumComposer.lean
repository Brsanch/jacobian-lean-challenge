/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationSumEqualsDegree
import JacobianChallenge.Manifold.DegreeUnconditional
import JacobianChallenge.Manifold.RegularValueExistsUnconditional
import JacobianChallenge.Manifold.FibreCardWellDefinedAtRegular

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Conditional discharge of `ramificationSumEqualsDegree_statement`

This file gives a structural reduction: from a packaged hypothesis
describing the analytic Hurwitz "near-y regular witness with matching
ramification sum" content, plus the standard regular-witness
companions, the named obligation
`Owed.degree.ramificationSumEqualsDegree_statement X Y` follows.

## Architecture (correction over the reverted RH5 attempt)

The previous attempt (RH5) invented a `HurwitzGlobalPackaging`
structure that — at branch values `y` where `f` actually ramifies —
required the cardinality of `f ⁻¹' {y}` itself to equal the sum of
ramification indices over `y`. This is provably false at branch
points (counts drop at branches), so that structure was uninhabitable
at branch values.

The correct route, given the discipline rules, is to package the
*classical Hurwitz output* directly: for every non-constant `f` and
every `y : Y`, there exists a *nearby* regular value `w`
(a `RegularValueWitnessReg f`) whose fibre cardinality equals
`∑_{x ∈ fibre y} manifoldRamificationIndex f x`. This shape is correct
because:

* at a regular `w`, the fibre is unramified and `|f ⁻¹' {w}|` legitimately
  counts the sheets;
* the planar Hurwitz local normal form (`analytic_local_normal_form`,
  `localKFoldMultiplicity_preimage_card_fully_unconditional`) shows
  that for `w` close to `y`, the count of preimages is exactly
  `∑_{x ∈ fibre y} k_x`, where `k_x = manifoldRamificationIndex f x`;
* at a regular `w`, `w.card = degreeFiber f hf` via
  `degreeFiber_eq_witness_card_at_regular`
  (`Manifold/DegreeUnconditional.lean`).

This file composes those three observations into a clean reduction.
The analytic content (existence of the near-y regular witness with the
ramification-sum property) is the `h_pkg` hypothesis the file consumes;
discharging it is a separate analytic chip.

## What this file delivers

* `ramificationSumEqualsDegree_holds_of_nearby_regular_witness`: the
  named obligation, discharged from a single `h_pkg` hypothesis
  bundling the classical Hurwitz outputs at this pin.

The file is a pure structural composer: no analytic content is assumed
beyond what is stated in `h_pkg`, and no axiom is introduced.

## Anti-cheat

* No `sorry`, no `axiom`.
* No signature change to anything outside this new file.
* `h_pkg` is a `Prop`-shaped reduction hypothesis stated inline, not a
  structure invented in this file. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-! ## The packaged Hurwitz output

For a non-constant analytic `f : X → Y` between compact connected
complex 1-manifolds, the classical Hurwitz local normal form together
with compactness of `X` produces, at each `y : Y`, a *nearby* regular
value `w` whose fibre cardinality equals the sum of local ramification
indices over `y`'s fibre. The hypothesis statement below names this
output. -/

/-- **Hurwitz near-`y` regular-witness existence (analytic input).**

For every non-constant analytic `f : X → Y` between compact connected
complex 1-manifolds and every `y : Y`, there exists a regular-value
witness `w : RegularValueWitnessReg f` whose fibre cardinality equals
the sum of local ramification indices over `y`'s fibre.

This is the analytic Hurwitz total-weight identity, packaged as a
single `Prop`. Discharging it is a separate analytic chip composing:
the Hurwitz local normal form (`analytic_local_normal_form`), the
planar k-fold count
(`localKFoldMultiplicity_preimage_card_fully_unconditional`), the
preimage eventual-containment lemma
(`preimage_eventually_in_fibre_neighbourhoods`), and the
finiteness-of-critical-values argument that delivers a *regular*
nearby `w`. -/
def NearbyRegularWitnessHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (y : Y),
    ∃ (w : RegularValueWitnessReg f),
      (w.card : ℕ) =
        (∑ x ∈ (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
          JacobianChallenge.Manifold.manifoldRamificationIndex f x)

/-- **The classical-choice regularity certificate (auxiliary input).**

Standard companion to `NearbyRegularWitnessHypothesis`: the
`Classical.choice`-selected witness behind `degreeFiber`'s body has a
regular value (zero critical preimages). This is needed to bridge
`degreeFiber f hf = (Classical.choice h_exist).card` to
`(Classical.choice h_exist).toRegular _ . card`. -/
def ClassicalChoiceRegularHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
    ∀ (h_exist : Nonempty (RegularValueWitness f)),
      ∀ x ∈ f ⁻¹' {(Classical.choice h_exist).value},
        deriv ((chartAt ℂ (Classical.choice h_exist).value) ∘ f ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) ≠ 0

/-! ### Regular-witness card well-definedness (item 3.reg).

Already named as `Owed.degree.fibre_card_well_defined_at_regular_statement`
in `Manifold/Degree.lean`; we re-use that exact statement here as the
companion hypothesis the composer consumes. -/

/-! ## Structural reduction

Given the named near-y witness hypothesis plus the standard
regular-witness companions, the named obligation follows by
unfolding both sides and identifying via
`degreeFiber_eq_witness_card_at_regular`. -/

/-- **Conditional discharge of the ramification-sum identity.**

From three packaged inputs:

* `h_near_y` (the analytic Hurwitz output: existence of a near-`y`
  regular witness whose card equals `∑ k_x`),
* `h_choice_reg` (the classical-choice regularity companion), and
* `h_wd_reg` (`fibre_card_well_defined_at_regular_statement`),

the named obligation `ramificationSumEqualsDegree_statement X Y`
follows by composition with `degreeFiber_eq_witness_card_at_regular`.

This is the corrected reduction route: the proof routes through a
nearby *regular* `w` (where `w.card = degreeFiber f hf` and also
`w.card = ∑ k_x`), not through `y` itself (where `|fibre y|` would
generally differ from `∑ k_x` at branch points). -/
theorem ramificationSumEqualsDegree_holds_of_nearby_regular_witness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_near_y : NearbyRegularWitnessHypothesis X Y)
    (h_choice_reg : ClassicalChoiceRegularHypothesis X Y)
    (h_wd_reg : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card) :
    JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y := by
  -- Unfold the named obligation.
  intro f hf hnc y
  -- Step 1: regular-value existence (unconditional at this pin).
  have h_exist : Nonempty (RegularValueWitness f) :=
    regular_value_exists_statement_holds_unconditional f hf hnc
  -- Step 2: extract the near-y regular witness from the package.
  obtain ⟨w, h_w_card⟩ := h_near_y f hf hnc y
  -- Step 3: pull the classical-choice regularity certificate.
  have h_b : ∀ x ∈ f ⁻¹' {(Classical.choice h_exist).value},
      deriv ((chartAt ℂ (Classical.choice h_exist).value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    h_choice_reg f hf hnc h_exist
  -- Step 4: pull the well-definedness on regular witnesses.
  have h_c : ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card :=
    h_wd_reg f hf hnc
  -- Step 5: identify `degreeFiber f hf = w.card` via the bridge in
  -- `DegreeUnconditional.lean`.
  have h_deg :
      JacobianChallenge.ContMDiff.degreeFiber f hf = w.card :=
    JacobianChallenge.ContMDiff.degreeFiber_eq_witness_card_at_regular
      f hf hnc h_exist h_b w h_c
  -- Step 6: combine `w.card = ∑ k_x` (from h_near_y) with
  -- `degreeFiber f hf = w.card` (h_deg) to conclude.
  -- Goal: ∑ ... = degreeFiber f hf
  rw [h_deg]
  -- Goal: ∑ ... = w.card
  exact h_w_card.symm

/-! ## Convenience: bundled hypothesis form

It is convenient downstream to bundle all three reduction hypotheses
into a single `Prop`. -/

/-- **Bundled hypothesis** for the conditional discharge: combines the
near-y witness existence, classical-choice regularity, and
regular-witness card well-definedness. -/
def RamificationSumPackage
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  NearbyRegularWitnessHypothesis X Y ∧
  ClassicalChoiceRegularHypothesis X Y ∧
  (∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
    ¬ JacobianChallenge.IsConstantMap f →
    ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card)

/-- **Bundled-form discharge.** Same content as
`ramificationSumEqualsDegree_holds_of_nearby_regular_witness`, with all
three inputs gathered into a single `RamificationSumPackage`. -/
theorem ramificationSumEqualsDegree_holds_of_package
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_pkg : RamificationSumPackage X Y) :
    JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y :=
  ramificationSumEqualsDegree_holds_of_nearby_regular_witness
    h_pkg.1 h_pkg.2.1 h_pkg.2.2

end Owed.degree
end ContMDiff
end JacobianChallenge
