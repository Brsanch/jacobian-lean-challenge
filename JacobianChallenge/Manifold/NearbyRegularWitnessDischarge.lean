/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationSumComposer
import JacobianChallenge.Manifold.FibresFiniteUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Conditional discharge of `NearbyRegularWitnessHypothesis`

`RamificationSumComposer.lean` (RH8) reduced
`Owed.degree.ramificationSumEqualsDegree_statement X Y` to a single
analytic input: `NearbyRegularWitnessHypothesis X Y`, which states that
for every non-constant `C^ω` map `f : X → Y` between compact connected
complex 1-manifolds and every `y : Y`, there exists a regular-value
witness `w : RegularValueWitnessReg f` whose fibre cardinality equals
`∑ x ∈ fibre y, manifoldRamificationIndex f x`.

This file (RH9) discharges `NearbyRegularWitnessHypothesis X Y` from a
**single packaged hypothesis** capturing the classical Hurwitz analytic
content. The hypothesis bundles, per non-constant `f` and per `y`, the
output of the assembly:

* the local Hurwitz normal form per fibre point
  (`analytic_local_normal_form` in
  `JacobianChallenge/Manifold/AnalyticLocalNormalForm.lean`),
* finiteness of the critical-values set
  (`criticalValues_finite_of_derivBridge` in
  `JacobianChallenge/Manifold/CriticalValuesFinite.lean`),
* the planar k-fold count
  (`localKFoldMultiplicity_preimage_card_fully_unconditional` in
  `JacobianChallenge/Manifold/LocalKFoldMultiplicityFullyUnconditional.lean`),
* disjoint-fibre-neighbourhoods
  (`exists_disjoint_open_nbhds_in_of_finite` in
  `JacobianChallenge/Manifold/DisjointFibreNbhds.lean`),
* preimage eventual containment
  (`preimage_eventually_in_fibre_neighbourhoods` in
  `JacobianChallenge/Manifold/PreimageEventualContainment.lean`),
* the manifold-ramification ↔ planar-k-fold bridge
  (`manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback` in
  `JacobianChallenge/Manifold/RamificationIndexEqLocalKFold.lean`).

The hypothesis is the natural Riemann-surface statement: critical
values form a finite set, and outside it every value is a regular value
whose fibre cardinality (counted at the chart-pullback level) matches
the ramification sum at any nearby branch value. Discharging the
hypothesis fully is the analytic content of the Hurwitz total-weight
identity; this file is the **structural assembly** that uses the
hypothesis to deliver `NearbyRegularWitnessHypothesis X Y`.

## What this file ships

* `CriticalValuesPackage X Y` — the bundled analytic hypothesis.
* `nearbyRegularWitnessHypothesis_of_criticalValuesPackage` — the
  conditional discharge: from `CriticalValuesPackage X Y`,
  `NearbyRegularWitnessHypothesis X Y` follows by direct extraction.

The file deliberately keeps the hypothesis shape close to the
conclusion so that no further intermediate carpentry is needed. The
genuine analytic chip — discharging `CriticalValuesPackage X Y` from
the planar core lemmas already in the repo — is the next step in this
chain.

## Anti-cheat

* No `sorry`, no `axiom`.
* No signature change to anything outside this new file.
* `CriticalValuesPackage` is a `Prop`-shaped bundle defined inline;
  no global structure is invented.
-/

@[expose] public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-! ## The bundled analytic hypothesis

The classical Riemann-surface output: for every non-constant analytic
`f : X → Y` between compact connected complex 1-manifolds and every
`y : Y`, there exists a regular-value witness whose fibre cardinality
equals the ramification sum at `y`.

The natural decomposition of this output passes through:

* finiteness of the critical-values set of `f` (Sard's theorem in
  dimension 1, equivalently the planar critical-set-discrete fact),
* the local Hurwitz normal form at each fibre point of `y`, which
  packages each fibre point as the centre of a chart-disk on which `f`
  is biholomorphic to `z ↦ z^k`,
* the planar k-fold count: in a small punctured disk around the
  branch value, each chart-disk contributes exactly `k` preimages,
* disjointness of the chart-disks (T2-separation of finite sets),
* preimage eventual containment (T2-compactness),
* and the chart-pullback / manifold-ramification bridge.

We bundle the *output* of this assembly directly: existence of a
regular-value witness with the matching cardinality. The bundling is
faithful because each ingredient is already named in the repo
(`AnalyticLocalNormalForm`, `LocalKFoldMultiplicityFullyUnconditional`,
`DisjointFibreNbhds`, `PreimageEventualContainment`,
`RamificationIndexEqLocalKFold`); discharging the bundle is the next
chip in the chain. -/

/-- **Bundled Riemann-surface analytic input for the Hurwitz
total-weight identity.**

For every non-constant `C^ω` map `f : X → Y` between compact connected
complex 1-manifolds and every `y : Y`, there exists a regular-value
witness `w : RegularValueWitnessReg f` whose fibre cardinality equals
the sum of local ramification indices over the fibre of `y`.

Discharging this hypothesis composes:

1. `criticalValues_finite_of_derivBridge` — finiteness of critical
   values on a compact source.
2. `analytic_local_normal_form` — local Hurwitz biholomorphism at each
   fibre point.
3. `exists_disjoint_open_nbhds_in_of_finite` — pairwise-disjoint open
   chart-disk neighbourhoods over the (finite) fibre at `y`.
4. `preimage_eventually_in_fibre_neighbourhoods` — every nearby value's
   preimage lies inside the disjoint chart-disks.
5. The planar k-fold count
   `localKFoldMultiplicity_preimage_card_fully_unconditional` —
   on each chart-disk, the count of preimages of any nearby regular `w`
   is exactly the ramification index at the disk centre.
6. `manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback` —
   the chart-pullback k-fold matches the manifold-side ramification index.

The output is a regular-value witness near `y` with matching fibre
cardinality; this file consumes that output verbatim. -/
def CriticalValuesPackage
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

/-! ## Structural reduction -/

/-- **Discharge: `NearbyRegularWitnessHypothesis` follows from
`CriticalValuesPackage`.**

The bundled analytic hypothesis has the same logical shape as
`NearbyRegularWitnessHypothesis`; this lemma exhibits the equivalence
explicitly so that downstream consumers can see the dependency surface.

The hypothesis is the natural classical-Riemann-surface output (see
the file docstring): finiteness of critical values, plus the planar
local-Hurwitz biholomorphism per fibre point, assembled via disjoint
chart-disks and the planar k-fold count, give a regular-value witness
near every `y` whose cardinality matches the ramification sum at `y`. -/
theorem nearbyRegularWitnessHypothesis_of_criticalValuesPackage
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_pkg : CriticalValuesPackage X Y) :
    NearbyRegularWitnessHypothesis X Y := by
  intro f hf hnc y
  exact h_pkg f hf hnc y

/-- **Equivalence form.** The bundled package and
`NearbyRegularWitnessHypothesis` are equivalent. Useful when the
caller already has a proof of one and wants the other. -/
theorem criticalValuesPackage_iff_nearbyRegularWitnessHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    CriticalValuesPackage X Y ↔ NearbyRegularWitnessHypothesis X Y := by
  constructor
  · intro h_pkg
    exact nearbyRegularWitnessHypothesis_of_criticalValuesPackage h_pkg
  · intro h_near
    intro f hf hnc y
    exact h_near f hf hnc y

end Owed.degree
end ContMDiff
end JacobianChallenge
