/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreCardOnRegularSubset
import JacobianChallenge.Manifold.RegularSubsetPreconnected

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Composition: Hurwitz local-constancy + finite-complement-preconnected
⇒ `fibre_card_well_defined_at_regular_statement` (ZZ155)

## Goal

Compose three structurally-independent pieces:

* **ZZ134** (`fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`,
  in `JacobianChallenge.Manifold.FibreCardOnRegularSubset`): from
  (a) an `IsLocallyConstant` of a fibre-cardinality readout on `Cᶜ` and
  (b) `IsPreconnected (Set.univ : Set (Cᶜ : Set Y))`,
  conclude the regular-form `fibre_card_well_defined_at_regular_statement`.

* **ZZ153** (in flight; see branch `feat/zz153-chip`): the `IsLocallyConstant`
  input is provided by `fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz`,
  which takes a pointwise Hurwitz patching package on `R ⊆ Y` and returns
  `IsLocallyConstant (fun y : R => (f ⁻¹' {y.val}).ncard)`. ZZ153 is **not yet
  on `main`**, so we do not import it; instead, we **parameterise this file
  on the literal `IsLocallyConstant` shape that ZZ153 will provide**, so a
  one-line discharge becomes available downstream the moment ZZ153 lands.

* **ZZ154** (`regularSubset_isPreconnected_of_finite_complement_hypothesis`,
  in `JacobianChallenge.Manifold.RegularSubsetPreconnected`): from a
  topological "complement of finite is preconnected" hypothesis, get
  `IsPreconnected (Set.univ : Set (Cᶜ : Set Y))`.

This file's contribution is the structural glue that pipes the
`ncard`-shaped local-constancy from ZZ153 into the
`Set.Finite.toFinset.card`-shaped `h_witness` premise of ZZ134, via the
standard `Set.ncard_eq_toFinset_card` bridge already used in
`BranchedCoverDegree` and `FiberCountBridge`.

## What is delivered

* `fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo` —
  the named composition: takes ZZ153-shaped `h_lc` and ZZ154-shaped
  `h_topo`, returns `fibre_card_well_defined_at_regular_statement X Y`.

No `sorry`. No `axiom`. No signature changes outside this file. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ContMDiff

namespace Owed.degree

universe u v

/-- **The ZZ155 composition.** Given:

* `h_lc` — the *literal output shape* of ZZ153's
  `fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz`: for every
  non-constant analytic `f : X → Y` and every critical-value set `C`,
  the fibre-cardinality readout `fun y : Cᶜ => (f ⁻¹' {y.val}).ncard` is
  locally constant on the subtype `Cᶜ`.

* `h_topo` — the topological "connected complex 1-manifold minus a finite
  set is preconnected" fact: for every finite `C : Set Y`, the complement
  `Cᶜ` is preconnected in `Y`.

* `h_C_fin` — the chosen critical-value sets are finite (the user supplies
  a finiteness witness per `f`; in the canonical use-case `C := f ''
  criticalSet f`, finite by ZZ48-class fibre-finiteness reasoning, but
  any finite `C` works).

Conclude `fibre_card_well_defined_at_regular_statement X Y`. -/
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
    fibre_card_well_defined_at_regular_statement X Y := by
  -- Specialise ZZ134's reduction.
  apply fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant
  intro f hf hnc C
  -- The fibre-cardinality function on all of `Y`, in `ncard` form.
  refine ⟨fun y => (f ⁻¹' {y}).ncard, ?_, ?_, ?_⟩
  · -- `card_of w.value = w.card` via the standard ncard ↔ toFinset.card bridge.
    intro w
    classical
    show (f ⁻¹' {w.value}).ncard = w.fiber_finite.toFinset.card
    exact Set.ncard_eq_toFinset_card (f ⁻¹' {w.value}) w.fiber_finite
  · -- Local-constancy on `Cᶜ`: literal ZZ153 shape.
    exact h_lc f hf hnc C
  · -- Subtype preconnectedness from ZZ154 + finite-complement hypothesis.
    have hCfin : C.Finite := h_C_fin f hf hnc C
    exact JacobianChallenge.Manifold.regularSubset_isPreconnected_of_finite_complement_hypothesis
      h_topo C hCfin

end Owed.degree

end ContMDiff

end JacobianChallenge
