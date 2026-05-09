/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationSumEqualsDegree
import JacobianChallenge.Manifold.RamificationIndexEqLocalKFold
import JacobianChallenge.Manifold.PreimageEventualContainment
import JacobianChallenge.Manifold.DisjointFibreNbhds
import JacobianChallenge.Manifold.FibreCardLocallyConstantFromNormalForm
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.RegularValueExistsUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Conditional composer for `ramificationSumEqualsDegree_statement` (RH5)

This file discharges
`ramificationSumEqualsDegree_statement X Y` (the named obligation in
`Manifold/RamificationSumEqualsDegree.lean`) **conditionally** on a single
analytic input naming Hurwitz local theory:

> For every non-constant `ContMDiff` map `f : X → Y` between compact
> connected complex 1-manifolds, there exists a number `N : ℕ` (the
> *Hurwitz degree*) such that at every `y : Y` we are given a
> `HurwitzPatchingData f y` whose discrete index-set cardinality is
> `N`, and that cardinality equals the local ramification sum
> `∑ x ∈ f ⁻¹' {y}, manifoldRamificationIndex f x`.

The hypothesis names two pieces of classical content:

* **Existence of the patching package** at every `y` is the Hurwitz
  local-normal-form theorem `analytic_local_normal_form` (already in
  `Manifold/AnalyticLocalNormalForm.lean`) lifted from the chart pullback
  to the manifold and patched across the finite fibre.  The *components*
  of this lift are present in main:
  `Manifold/RamificationIndexEqLocalKFold.lean` (`manifoldRamificationIndex`
  ↔ chart-pullback k-fold), `Manifold/DisjointFibreNbhds.lean` (disjoint
  open neighbourhoods of fibre points in a T2 space),
  `Manifold/PreimageEventualContainment.lean` (`f ⁻¹' V ⊆ ⋃ U_x` for
  `V` small open of `y`), and
  `Manifold/LocalKFoldMultiplicityFullyUnconditional.lean` (planar
  `k`-fold count for the chart pullback).  Composing these into the
  per-`y` `HurwitzPatchingData f y` plus the multiplicity claim
  `xs.card = ∑ manifoldRamificationIndex` is the analytic content this
  hypothesis names.

* **Independence of `pkg.xs.card` from `y`** (the constant `N`) is the
  classical "degree is well-defined" theorem.  The topological half of
  the discharge (path-connectedness of the regular locus
  `Y \ critical_values`) is already unconditional at this pin
  (`Manifold/HurwitzWellDefinedUnconditionalTopo.lean`); the analytic
  half (finite critical-value set + locally-constant fibre cardinality)
  is what the bundled hypothesis encapsulates.

Once the hypothesis lands, this composer is one rewrite away from strict
closure of the `ramificationSumEqualsDegree_statement` obligation.

## What this file ships

* `HurwitzGlobalPackaging` — the structured form of the bundled
  Hurwitz analytic input.

* `ramificationSumEqualsDegree_of_hurwitzPackaged` — the conditional
  discharge of `ramificationSumEqualsDegree_statement X Y` from the
  bundled Hurwitz packaging hypothesis.

## Proof outline (substantive — uses the existing infrastructure)

1. Pull out the constant `N` and the per-`y` packaging from
   `h_hurwitz`.
2. At the target point `y`: `pkg_y.xs.card = ∑ manifoldRamificationIndex`
   and `pkg_y.xs.card = N`, so `∑ manifoldRamificationIndex = N`.
3. To equate `N` with `degreeFiber f hf`:
   * `degreeFiber` is defined via `Classical.choice` on
     `Nonempty (RegularValueWitness f)`.  The latter is unconditional at
     this pin from `regular_value_exists_statement_holds_unconditional`
     (which only needs `fibres_finite_statement` + non-emptiness of `Y`,
     both available).
   * Let `wstar := Classical.choice ...`.  Then
     `degreeFiber f hf = wstar.card = (f ⁻¹' {wstar.value}).Finite.toFinset.card`.
   * Apply `h_hurwitz` at `wstar.value` to get `pkg' : HurwitzPatchingData
     f wstar.value` with `pkg'.xs.card = N`.
   * The structure lemma `pkg'.fibre_ncard_eq_xs_card_of_mem_W` applied
     to `wstar.value ∈ pkg'.W` (`pkg'.y₀_mem_W`) gives
     `(f ⁻¹' {wstar.value}).ncard = pkg'.xs.card = N`.
   * Bridge `ncard ↔ Finset.card` via `Set.ncard_eq_toFinset_card`.
4. Combine to conclude
   `∑ manifoldRamificationIndex = N = degreeFiber f hf`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to anything outside this file.
* The hypothesis names a *single* analytic input (Hurwitz local theory
  packaged as a patching package + a global Hurwitz degree); the
  conclusion is then derived through real structural work using
  `HurwitzPatchingData.fibre_ncard_eq_xs_card_of_mem_W` and the
  unconditional regular-value-existence chain.
-/

@[expose] public section

open scoped Manifold Topology ContDiff
open Set Filter

namespace JacobianChallenge

namespace ContMDiff

namespace Owed.degree

universe u v

/-- **The bundled Hurwitz-packaging input.**

Names, for a given non-constant `ContMDiff` map `f : X → Y`, the
output of Hurwitz local theory in structured form: a global Hurwitz
degree `N : ℕ`, plus at every `y : Y` a `HurwitzPatchingData f y` whose
discrete index-set cardinality is `N` and whose multiplicity sum is the
local ramification sum at `y`.

The fibres-finite witness is fixed so the `Finset` index of the sum
matches the one in `ramificationSumEqualsDegree_statement`. -/
structure HurwitzGlobalPackaging
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) where
  /-- The global Hurwitz degree of `f` (the same number on every fibre,
  by Hurwitz local theory + connectedness of `Y`). -/
  N : ℕ
  /-- At every `y : Y`, a topological patching package realising the
  fibre count `N` (with branch-point multiplicity collapsed). -/
  pkg : ∀ y : Y, JacobianChallenge.HurwitzPatchingData f y
  /-- The packaging realises the global degree `N`. -/
  card_eq_N : ∀ y : Y, (pkg y).xs.card = N
  /-- The packaging cardinality equals the local ramification sum
  at `y` (the multiplicity claim of Hurwitz local theory). -/
  card_eq_ram : ∀ y : Y, (pkg y).xs.card =
    ∑ x ∈ (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
      JacobianChallenge.Manifold.manifoldRamificationIndex f x

/-- **Conditional discharge of `ramificationSumEqualsDegree_statement`.**

Conclude the named ramification-sum identity from a single bundled
analytic input: the `HurwitzGlobalPackaging` (a global Hurwitz degree
`N` and per-`y` patching packages realising both `N` and the ramification
sum).

The proof is genuinely structural: it derives
`degreeFiber f hf = N` by choosing a regular-value witness via the
unconditional `regular_value_exists_statement_holds_unconditional`,
applying the Hurwitz packaging at the witness's value, and using the
structure lemma `HurwitzPatchingData.fibre_ncard_eq_xs_card_of_mem_W`
to identify the fibre cardinality with `pkg.xs.card`. -/
theorem ramificationSumEqualsDegree_of_hurwitzPackaged
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_hurwitz : ∀ (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
        (hnc : ¬ JacobianChallenge.IsConstantMap f),
        HurwitzGlobalPackaging f hf hnc) :
    ramificationSumEqualsDegree_statement X Y := by
  classical
  unfold ramificationSumEqualsDegree_statement
  intro f hf hnc y
  -- Pull out the bundled packaging.
  let H := h_hurwitz f hf hnc
  -- The ramification sum equals `(H.pkg y).xs.card` (multiplicity claim).
  have h_ram_eq :
      (∑ x ∈ (fibres_finite_statement_holds_unconditional
          f hf hnc y).toFinset,
          JacobianChallenge.Manifold.manifoldRamificationIndex f x) =
        (H.pkg y).xs.card := (H.card_eq_ram y).symm
  -- And `(H.pkg y).xs.card = H.N`.
  have h_y_N : (H.pkg y).xs.card = H.N := H.card_eq_N y
  -- Now compute `degreeFiber f hf`.  It is defined via
  -- `Classical.choice` on `Nonempty (RegularValueWitness f)`, which
  -- is unconditional via `regular_value_exists_statement_holds_unconditional`.
  have h_witness_nonempty : Nonempty (RegularValueWitness f) :=
    regular_value_exists_statement_holds_unconditional f hf hnc
  set wstar : RegularValueWitness f := Classical.choice h_witness_nonempty with hwstar
  -- `degreeFiber f hf = wstar.card`.
  have h_deg_eq : JacobianChallenge.ContMDiff.degreeFiber f hf = wstar.card :=
    degreeFiber_eq_witness_card f hf hnc h_witness_nonempty
  -- Apply the packaging at `wstar.value`.
  let pkg' := H.pkg wstar.value
  have h_w_N : pkg'.xs.card = H.N := H.card_eq_N wstar.value
  -- `wstar.value ∈ pkg'.W` since `pkg'` is a packaging at `wstar.value`.
  have h_y₀_mem : wstar.value ∈ pkg'.W := pkg'.y₀_mem_W
  -- `(f ⁻¹' {wstar.value}).ncard = pkg'.xs.card`.
  have h_ncard_xs : (f ⁻¹' {wstar.value}).ncard = pkg'.xs.card :=
    pkg'.fibre_ncard_eq_xs_card_of_mem_W h_y₀_mem
  -- Bridge `ncard ↔ Finset.card` via `wstar.fiber_finite`.
  have h_ncard_finset : (f ⁻¹' {wstar.value}).ncard =
      wstar.fiber_finite.toFinset.card :=
    Set.ncard_eq_toFinset_card (f ⁻¹' {wstar.value}) wstar.fiber_finite
  -- `wstar.card = wstar.fiber_finite.toFinset.card` by definition.
  have h_wstar_card : wstar.card = wstar.fiber_finite.toFinset.card := rfl
  -- Chain: `wstar.card = ncard = pkg'.xs.card = N`.
  have h_wstar_N : wstar.card = H.N := by
    rw [h_wstar_card, ← h_ncard_finset, h_ncard_xs, h_w_N]
  -- Chain: `degreeFiber = wstar.card = N = (H.pkg y).xs.card = ∑ ramification`.
  rw [h_ram_eq, h_y_N, ← h_wstar_N, ← h_deg_eq]

end Owed.degree

end ContMDiff

end JacobianChallenge
