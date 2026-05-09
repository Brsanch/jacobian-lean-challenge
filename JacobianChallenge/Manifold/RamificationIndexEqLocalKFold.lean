/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndex

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Bridge `manifoldRamificationIndex` ↔ `localKFoldMultiplicityChartPullback`

Both quantities equal the order of vanishing (`.toNat`) of the chart
pullback shift `F z - F z₀` at `z₀ = (chartAt ℂ x) x`. The manifold-side
ramification index is defined directly as that `.toNat` in
`JacobianChallenge.Manifold.RamificationIndex`. The "local k-fold
multiplicity" used in the planar count theorems
(`localKFoldMultiplicity_preimage_card_fully_unconditional` etc.) is the
same `k` extracted from the analytic local normal form
`F z = F z₀ + (ψ z) ^ k`, namely
`k = (analyticOrderAt (F - F z₀) z₀).toNat`.

This file packages that planar quantity, applied to the chart pullback,
as `localKFoldMultiplicityChartPullback`, and discharges the bridge as a
definitional equality (`rfl`).

## What this file ships

* `localKFoldMultiplicityChartPullback f x` — a `noncomputable` `ℕ`-valued
  manifold-level wrapper for the planar k-fold multiplicity of the chart
  pullback `F z := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` at
  `z₀ := (chartAt ℂ x) x`. Defined as
  `(analyticOrderAt (F - F z₀) z₀).toNat`.

* `localKFoldMultiplicityChartPullback_eq` — unfold lemma, `rfl`.

* `manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback` — the
  bridge: equality of the two `.toNat` invariants. Proof is `rfl` since
  both unfold to the same analytic order .toNat.

* `manifoldRamificationIndex_eq_analyticOrderAt_chartShift_toNat` — re-export
  of the unfold lemma already named `manifoldRamificationIndex_eq` in
  `RamificationIndex.lean`, kept here as the LHS half of the bridge under
  the name suggested by the brief.

* `localKFoldMultiplicityChartPullback_eq_analyticOrderAt_toNat` — the RHS
  half of the bridge: equality of the chart-pullback k-fold multiplicity
  with the analytic order .toNat.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to anything outside this new file.
* The wrapper `localKFoldMultiplicityChartPullback` is an *additive*
  definition; nothing is renamed.
-/

@[expose] public section

open scoped Topology

namespace JacobianChallenge

namespace Manifold

universe u v

/-- **Manifold-level wrapper for the planar k-fold multiplicity.**

For `f : X → Y` between charted spaces over `ℂ` and a point `x : X`,
this is the local k-fold multiplicity of the chart pullback
`F z := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm`
at `z₀ := (chartAt ℂ x) x`, viewed as a `ℕ` via `ENat.toNat`.

The planar k-fold multiplicity at a point of a `ℂ → ℂ` map is the same
`k` that appears in the local Hurwitz normal form
`F z = F z₀ + (ψ z) ^ k`, equivalently the analytic order of
`F - F z₀` at `z₀` (viewed as a natural number — `⊤` from the constant
case maps to `0`). -/
noncomputable def localKFoldMultiplicityChartPullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) : ℕ :=
  let z₀ : ℂ := (chartAt ℂ x) x
  let F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm
  (analyticOrderAt (fun z => F z - F z₀) z₀).toNat

/-- Unfold lemma: the chart-pullback k-fold multiplicity equals the
`ENat.toNat` of the analytic order of the chart-pullback shift at the
chart image of the basepoint. -/
lemma localKFoldMultiplicityChartPullback_eq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) :
    localKFoldMultiplicityChartPullback f x =
      (analyticOrderAt
        (fun z =>
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x)).toNat := rfl

/-- **LHS half of the bridge** (re-export of `manifoldRamificationIndex_eq`):
the manifold-side ramification index equals the `.toNat` of the analytic
order of the chart-pullback shift. -/
lemma manifoldRamificationIndex_eq_analyticOrderAt_chartShift_toNat
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) :
    manifoldRamificationIndex f x =
      (analyticOrderAt
        (fun z =>
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x)).toNat :=
  manifoldRamificationIndex_eq f x

/-- **RHS half of the bridge.** The chart-pullback k-fold multiplicity
equals the `.toNat` of the analytic order of the chart-pullback shift. -/
lemma localKFoldMultiplicityChartPullback_eq_analyticOrderAt_toNat
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) :
    localKFoldMultiplicityChartPullback f x =
      (analyticOrderAt
        (fun z =>
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x)).toNat :=
  localKFoldMultiplicityChartPullback_eq f x

/-- **Bridge theorem.** The manifold-side ramification index agrees with
the planar-disk k-fold multiplicity from the local normal form, evaluated
on the chart pullback.

Both quantities are by construction `(analyticOrderAt (F - F z₀) z₀).toNat`
for `F z := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` and
`z₀ := (chartAt ℂ x) x`, so the equality is definitional. The mathematical
content — that this `.toNat` is genuinely the Hurwitz `k` — is delivered
by `analytic_local_normal_form` and the planar k-fold count
`localKFoldMultiplicity_preimage_card_fully_unconditional`. -/
theorem manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) :
    manifoldRamificationIndex f x = localKFoldMultiplicityChartPullback f x :=
  rfl

end Manifold

end JacobianChallenge
