/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreCardOnRegularSubset
import JacobianChallenge.Manifold.RegularSubsetPreconnected

/-! # Composition: Hurwitz local-constancy + finite-complement-preconnected
⇒ `fibre_card_well_defined_at_regular_statement` (ZZ155)

Compose ZZ134 (`fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`)
+ ZZ153-shaped local constancy + ZZ154-shaped finite-complement-preconnected
into the named owed statement `fibre_card_well_defined_at_regular_statement X Y`.

This file is the structural glue. The unconditional unconditional
discharges of the two analytic hypotheses (ZZ153/ZZ157 chain for
local-constancy, ZZ154 for preconnected) plug straight in via the
parameterized hypothesis shapes this file consumes.

No `sorry`, no `axiom`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ContMDiff

namespace Owed.degree

universe u v

/-- **The ZZ155 composition.** Conditional on:

* `h_lc` — ZZ153-shape: the fibre-cardinality `(f ⁻¹' {y}).ncard` on `Cᶜ`
  is locally constant in subtype topology.
* `h_topo` — ZZ154-shape: complement of any finite set in `Y` is
  preconnected as a subset of `Y`.
* `h_C_fin` — chosen critical-value set `C` is finite (the canonical
  choice `C := f '' criticalSet f` will be finite by ZZ48-class
  fibre-finiteness; any finite `C` works).

Conclude the unfolded form of `fibre_card_well_defined_at_regular_statement X Y`.

Stated in the unfolded `∀ f hf hnc C w₁ w₂, w₁.card = w₂.card` shape rather
than against the def, to avoid `intro`-time elaboration "typeclass instance
problem is stuck" issues observed when applying the def directly. The
underlying statement is identical (the def's body). -/
theorem fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y),
        IsLocallyConstant (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard))
    (h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y))
    (h_C_fin : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f → ∀ (C : Set Y), C.Finite) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y) (w₁ w₂ : RegularValueWitnessReg f C), w₁.card = w₂.card := by
  -- Build the ZZ134-shape package and apply ZZ134.
  apply fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant
  intro f hf hnc C
  refine ⟨fun y => (f ⁻¹' {y}).ncard, ?_, ?_, ?_⟩
  · -- card_of w.value = w.card via ncard ↔ toFinset.card.
    intro w
    classical
    exact Set.ncard_eq_toFinset_card (f ⁻¹' {w.value}) w.fiber_finite
  · -- Local-constancy from h_lc.
    exact h_lc f hf hnc C
  · -- IsPreconnected (Set.univ : Set (Cᶜ : Set Y)) directly from ZZ154.
    exact JacobianChallenge.Manifold.regularSubset_isPreconnected_of_finite_complement_hypothesis
      h_topo C (h_C_fin f hf hnc C)

/-- **Definitional packaging** — the same composition delivered against the
def name `fibre_card_well_defined_at_regular_statement`. -/
theorem fibre_card_well_defined_at_regular_statement_holds_of_lc_ncard_and_topo
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_lc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (C : Set Y),
        IsLocallyConstant (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard))
    (h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y))
    (h_C_fin : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f → ∀ (C : Set Y), C.Finite) :
    fibre_card_well_defined_at_regular_statement X Y :=
  fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo (X := X) (Y := Y)
    h_lc h_topo h_C_fin

end Owed.degree

end ContMDiff

end JacobianChallenge
