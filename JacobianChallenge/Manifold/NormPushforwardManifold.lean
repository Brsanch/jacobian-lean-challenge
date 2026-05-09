/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.NormPushforwardMeromorphy
import JacobianChallenge.Manifold.NormPushforwardMeromorphyZero

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Manifold-level chart-pullback wrappers for the planar norm pushforward
(Phase 1 chip P1.1f, ZZ205)

This file lifts the planar `normPow g k` meromorphy results
(ZZ201 regular branch, ZZ204 unconditional `t = 0` branch) to the
manifold level via the chart at a target point `y₀ : Y`.

## What is shipped

For a topological space `Y` charted on `ℂ` (`[ChartedSpace ℂ Y]`) and a
point `y₀ : Y` with chart image `t₀ := (chartAt ℂ y₀) y₀`, we ship two
per-chart wrappers, both expressed in the chart-pullback meromorphy
predicate `MMeromorphicAt 𝓘(ℂ, ℂ) F y₀` from
`JacobianChallenge.Manifold.MeromorphicAt`:

* `normPow_mmeromorphicAt_chartPullback_zero` — at any `y₀` whose chart
  image is `0`, the chart-pulled-back planar norm pushforward
  `(normPow g k) ∘ (chartAt ℂ y₀)` is `MMeromorphicAt` at `y₀` whenever
  `g` is `MeromorphicAt 0` and `1 ≤ k`. Uses ZZ204.

* `normPow_mmeromorphicAt_chartPullback_regular` — at any `y₀` with a
  chart image `t₀ ≠ 0`, the chart pullback `(normPow g k) ∘ (chartAt ℂ y₀)`
  is `MMeromorphicAt` at `y₀` whenever `g` is `MeromorphicAt` at every
  point on the `μ_k`-orbit of any chosen `k`-th root `s₀` of `t₀`. Uses
  ZZ201.

These per-chart wrappers are the manifold-side payload for downstream
chips that need to glue them across all preimages of a target point of
a holomorphic map `f : X → Y`. The global gluing (a finite product over
`f⁻¹(y₀)`, with each factor a per-chart contribution from the source
side) is **deferred** to a follow-up chip — see "Residual" below.

## Why this granularity

The chip plan (P1.1f) explicitly recommends shipping a per-chart-pair
statement and treating the global product-over-preimage gluing as a
separate residual, since the global side requires importing the
finite-fibre + ramification-multiplicity bundle from
`Manifold/NearbyRegularWitnessUnconditional.lean` and
`Manifold/RamificationIndexEqLocalKFold.lean`, both of which already
sit on top of a substantial Hurwitz-local-form scaffolding
(`Manifold/AnalyticLocalNormalForm.lean`). The per-chart wrappers here
are exactly the planar-meromorphy → chart-pullback bridge that those
downstream chips will plug into.

## Residual

The **global** statement
```
normPushforwardManifold f g : Y → ℂ
normPushforwardManifold_mmeromorphicAt :
    MMeromorphicAt 𝓘(ℂ, ℂ) (normPushforwardManifold f g) y₀
```
where `f : X → Y` is non-constant `ContMDiff` and `g : MeromorphicNonzero X`
is a global meromorphic function on `X`, is **not** in this file. The
shape requires
* finiteness of `f⁻¹(y₀)` (already in `FibresFiniteUnconditional.lean`),
* per-source-chart Hurwitz local form `f = s ↦ s^k` (already in
  `AnalyticLocalNormalForm.lean`),
* ramification-index ↔ local-k-fold multiplicity bridge (already in
  `RamificationIndexEqLocalKFold.lean`),
* finite-product factorization
  `∏_{x ∈ f⁻¹(y)} g(x)^{ramif} = ∏_{source charts} (per-chart normPow)`,
* manifold-level `MMeromorphicAt` of a finite product (lifted from
  `MMeromorphicAt.mul` already in `Manifold/MeromorphicAt.lean`).

Each of these is independently available; gluing them is a separate
chip and is logged as residual P1.1g in `CLOSURE_MAP.md`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No `ω` binder anywhere (Lean 4.30 reserved).
* No signature change to any pre-existing definition or theorem.
* No edits to `JacobianChallenge.lean` other than adding the import.
-/

noncomputable section

open scoped Manifold Topology
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-! ### Chart-pullback eventual identity for `normPow g k`

The chart-pulled-back representative of `(normPow g k) ∘ (chartAt ℂ y₀)`
is the function
`((normPow g k) ∘ (chartAt ℂ y₀)) ∘ (chartAt ℂ y₀).symm`
which on the chart target `(chartAt ℂ y₀).target` agrees with
`normPow g k` itself (via the chart's `right_inv` axiom). Since
`(chartAt ℂ y₀).target` is open and contains the chart image
`(chartAt ℂ y₀) y₀`, the agreement holds on a neighbourhood of
the chart image, hence on the punctured-or-not filter used by
`MeromorphicAt.congr`. -/

/-- The chart-pulled-back representative of `(normPow g k) ∘ (chartAt ℂ y₀)`
agrees with `normPow g k` on the chart target. -/
private lemma normPow_chartPullback_eqOn_target
    (g : ℂ → ℂ) (k : ℕ) (y₀ : Y) :
    Set.EqOn (((normPow g k) ∘ (chartAt ℂ y₀)) ∘ (chartAt ℂ y₀).symm)
      (normPow g k) (chartAt ℂ y₀).target := by
  intro z hz
  show normPow g k ((chartAt ℂ y₀) ((chartAt ℂ y₀).symm z))
      = normPow g k z
  rw [(chartAt ℂ y₀).right_inv hz]

/-- The chart-pulled-back representative of `(normPow g k) ∘ (chartAt ℂ y₀)`
equals `normPow g k` on a neighbourhood of the chart image
`(chartAt ℂ y₀) y₀`. -/
private lemma normPow_chartPullback_eventuallyEq
    (g : ℂ → ℂ) (k : ℕ) (y₀ : Y) :
    (((normPow g k) ∘ (chartAt ℂ y₀)) ∘ (chartAt ℂ y₀).symm)
      =ᶠ[nhds ((chartAt ℂ y₀) y₀)] normPow g k := by
  refine Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨(chartAt ℂ y₀).target, ?_, normPow_chartPullback_eqOn_target g k y₀⟩
  exact (chartAt ℂ y₀).open_target.mem_nhds
    ((chartAt ℂ y₀).map_source (mem_chart_source ℂ y₀))

/-- Punctured-filter version of `normPow_chartPullback_eventuallyEq`. -/
private lemma normPow_chartPullback_eventuallyEq_nhdsNE
    (g : ℂ → ℂ) (k : ℕ) (y₀ : Y) :
    (((normPow g k) ∘ (chartAt ℂ y₀)) ∘ (chartAt ℂ y₀).symm)
      =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)] normPow g k :=
  (normPow_chartPullback_eventuallyEq g k y₀).filter_mono nhdsWithin_le_nhds

/-! ### Headline 1: branch value `t₀ = 0` (from ZZ204) -/

/-- **Manifold-level meromorphy of the chart-pulled-back norm pushforward
at the branch value.**

If the chart at `y₀` sends `y₀ ↦ 0`, and `g : ℂ → ℂ` is `MeromorphicAt` at
`0` with `1 ≤ k`, then the chart-pulled-back planar norm pushforward
`y ↦ normPow g k ((chartAt ℂ y₀) y)` is meromorphic at `y₀` in the
chart-pullback (manifold) sense.

This is the manifold-level wrapper of ZZ204
(`normPow_meromorphicAt_zero`). -/
theorem normPow_mmeromorphicAt_chartPullback_zero
    {y₀ : Y} (h_chart_zero : (chartAt ℂ y₀) y₀ = 0)
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : MeromorphicAt g 0) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (fun y : Y => normPow g k ((chartAt ℂ y₀) y)) y₀ := by
  -- Unfold `MMeromorphicAt` to the chart-pullback form.
  show MeromorphicAt
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y)) ∘ (chartAt ℂ y₀).symm)
      ((chartAt ℂ y₀) y₀)
  -- Rewrite the basepoint via `h_chart_zero`.
  rw [h_chart_zero]
  -- The composed function equals `normPow g k` on a neighbourhood of `0`
  -- (after rewriting the basepoint).
  have h_evEq :
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y)) ∘ (chartAt ℂ y₀).symm)
        =ᶠ[𝓝[≠] (0 : ℂ)] normPow g k := by
    have h := normPow_chartPullback_eventuallyEq_nhdsNE g k y₀
    -- `h` is at filter `𝓝[≠] ((chartAt ℂ y₀) y₀)`; rewrite to `𝓝[≠] 0`.
    rw [h_chart_zero] at h
    -- The function shape `((normPow g k) ∘ (chartAt ℂ y₀)) ∘ (chartAt ℂ y₀).symm`
    -- is definitionally equal to
    -- `(fun y => normPow g k ((chartAt ℂ y₀) y)) ∘ (chartAt ℂ y₀).symm`.
    exact h
  -- Apply `MeromorphicAt.congr` with the planar headline ZZ204.
  exact (normPow_meromorphicAt_zero hk hg).congr h_evEq.symm

/-! ### Headline 2: regular value `t₀ ≠ 0` (from ZZ201) -/

/-- **Manifold-level meromorphy of the chart-pulled-back norm pushforward
at a regular value.**

If the chart at `y₀` sends `y₀ ↦ t₀` with `t₀ ≠ 0`, and `g : ℂ → ℂ` is
`MeromorphicAt` at every point of the form `ζ * s₀` for `ζ` a `k`-th
root of unity (with `s₀` any chosen `k`-th root of `t₀`), then the
chart-pulled-back planar norm pushforward
`y ↦ normPow g k ((chartAt ℂ y₀) y)` is meromorphic at `y₀` in the
chart-pullback (manifold) sense.

This is the manifold-level wrapper of ZZ201
(`normPow_meromorphicAt_of_regular`). -/
theorem normPow_mmeromorphicAt_chartPullback_regular
    {y₀ : Y} {t₀ : ℂ} (h_chart_eq : (chartAt ℂ y₀) y₀ = t₀)
    (ht₀ : t₀ ≠ 0)
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    {s₀ : ℂ} (hs₀ : s₀ ^ k = t₀)
    (hg : ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
      MeromorphicAt g (ζ * s₀)) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (fun y : Y => normPow g k ((chartAt ℂ y₀) y)) y₀ := by
  -- Unfold `MMeromorphicAt`.
  show MeromorphicAt
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y)) ∘ (chartAt ℂ y₀).symm)
      ((chartAt ℂ y₀) y₀)
  rw [h_chart_eq]
  -- Eventual equality on `𝓝[≠] t₀`.
  have h_evEq :
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y)) ∘ (chartAt ℂ y₀).symm)
        =ᶠ[𝓝[≠] t₀] normPow g k := by
    have h := normPow_chartPullback_eventuallyEq_nhdsNE g k y₀
    rw [h_chart_eq] at h
    exact h
  -- Apply ZZ201.
  exact (normPow_meromorphicAt_of_regular g hk ht₀ hs₀ hg).congr h_evEq.symm

/-! ### Combined headline: both cases together -/

/-- **Manifold-level meromorphy of the chart-pulled-back norm pushforward
at any chart point.**

Combines `normPow_mmeromorphicAt_chartPullback_zero` (ZZ204) and
`normPow_mmeromorphicAt_chartPullback_regular` (ZZ201). The hypothesis
is supplied as a planar `MeromorphicAt (normPow g k) ((chartAt ℂ y₀) y₀)`
proof; downstream callers can supply this from either ZZ204 (when the
chart image is `0`) or ZZ201 (when the chart image is non-zero), or any
future strengthening. -/
theorem normPow_mmeromorphicAt_chartPullback_of_planar
    (y₀ : Y) (g : ℂ → ℂ) (k : ℕ)
    (h_planar : MeromorphicAt (normPow g k) ((chartAt ℂ y₀) y₀)) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (fun y : Y => normPow g k ((chartAt ℂ y₀) y)) y₀ := by
  show MeromorphicAt
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y)) ∘ (chartAt ℂ y₀).symm)
      ((chartAt ℂ y₀) y₀)
  exact h_planar.congr (normPow_chartPullback_eventuallyEq_nhdsNE g k y₀).symm

end Manifold
end JacobianChallenge

end
