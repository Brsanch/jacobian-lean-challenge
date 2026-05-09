/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.NormPushforwardGlobal
import JacobianChallenge.Manifold.NormPushforwardManifold

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Per-point meromorphy of `NormFM` from chart-local product witnesses
(Phase 1 chip P1.2b, ZZ207)

This file discharges the per-point `MMeromorphicAt` hypothesis that ZZ206
left as an input to `NormFM_mmeromorphicOn_univ_of_pointwise`, **conditional
on a chart-local product witness** at each `y₀ : Y`.

A chart-local product witness at `y₀` is the data of:
* a `Finset σ` indexing the fibre points (or any abstract index — the
  conclusion is independent of the cardinality up to having a finite
  index set);
* a family `F : σ → Y → ℂ` of factors, each `MMeromorphicAt I · y₀`;
* an eventual-equality witness, in chart-pullback form, between
  `NormFM f hf hf_nc g` and the `Finset` product of the factors near
  `y₀` (technically, between their chart-pullbacks on
  `𝓝[≠] (chartAt ℂ y₀ y₀)`).

The conclusion is `MMeromorphicAt (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) y₀`.

## Why the chart-local product witness is the right input

In the eventual full discharge of P1.2b, the `F i` factors will be
chart-pulled-back planar `normPow (g ∘ chart_xᵢ.symm ∘ ψᵢ.symm) kᵢ`
applied to `chartAt ℂ y₀ y - w₀`, with the eventual-equality coming from
the Hurwitz local form `t = w₀ + ψ^k` glued across the (finitely many)
fibre points. Each factor is `MMeromorphicAt` by ZZ205
(`normPow_mmeromorphicAt_chartPullback_zero`, after a constant
translation in the chart coordinate). The eventual-equality witness is
the combinatorial heart of P1.2b — the finite-fibre + ramification-
multiplicity bookkeeping coming from
`Manifold/NearbyRegularWitnessUnconditional.lean` and
`Manifold/RamificationIndexEqLocalKFold.lean`.

This file packages the **second half** of that argument — once both
ingredients (per-factor manifold meromorphy + chart-pullback eventual
equality of `NormFM` with the product) are in hand, the conclusion is
a clean `mmeromorphicAt_finset_prod` + `MeromorphicAt.congr` combination.

## What is shipped

* `MMeromorphicAt.congr_chartPullback` — a chart-pullback-form congr
  lemma for `MMeromorphicAt`. Given `f =ᶠ[𝓝[≠] (chartAt ℂ x x)] g` in
  the chart-pullback sense (i.e. on `f ∘ chart.symm`, `g ∘ chart.symm`),
  meromorphy of one transfers to the other.

* `NormFM_mmeromorphicAt_of_chartLocalProductWitness` — the chip's
  headline. Per-point `MMeromorphicAt` of `NormFM f hf hf_nc g` at `y₀`
  given (a) a `Finset` of factors each `MMeromorphicAt y₀`, and (b) a
  chart-pullback eventual-equality witness identifying `NormFM` with
  the `Finset` product near `y₀`.

* `NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses` — the
  global headline obtained by quantifying the per-point witness over
  `y₀ : Y`. Composes with
  `NormFM_mmeromorphicOn_univ_of_pointwise` from ZZ206.

## Residual

The two missing ingredients to get the unconditional headline:

1. **Per-factor production.** For each `y₀` and each fibre point
   `x ∈ f⁻¹{y₀}`, produce a factor `F_x : Y → ℂ` of the form
   `y ↦ normPow (g ∘ chart_x.symm ∘ ψ_x.symm) k_x ((chartAt ℂ y₀ y) - w₀)`
   (with `w₀ := chartAt ℂ y₀ y₀`) and prove `MMeromorphicAt I F_x y₀`.
   The shape calls for an off-by-translation form of ZZ205's
   `normPow_mmeromorphicAt_chartPullback_zero`, which can be obtained
   by a chart re-centering or by a direct planar
   `MeromorphicAt.comp`-by-translation argument.

2. **Eventual equality of `NormFM` with the chart-local product.** This
   is the combinatorial heart referenced above:
   * Use `localKFoldMultiplicityOnManifold_genuine_with_radius` to
     produce, for each fibre point `x ∈ f⁻¹{y₀}`, a small chart
     neighbourhood of `y₀` on which the preimages near `x` of any
     `y ∈ V \ {y₀}` are exactly the `k_x`-th roots of
     `chartAt y₀ y - w₀` after composition with `ψ_x`.
   * Intersect over the finite fibre to get a single neighbourhood.
   * Bijection between `(f⁻¹{y}).toFinset` and
     `⋃_x nthRootsFinset k_x (...)` on the punctured neighbourhood.
   * `Finset.prod`-rewrite plus `g.toFun x ^ ramif = (g ∘ ψ⁻¹)((root)) ^ k`
     under the bijection.

Both items are concrete and self-contained; each is a reasonable
follow-up chip (P1.2c and P1.2d). The current file ships the (clean)
glue between them and the ZZ206 headline.

## Anti-cheat

* No `axiom`, no `sorry`.
* No `ω` binder anywhere (Lean 4.30 reserved).
* No signature change to any pre-existing definition or theorem.
* Only one new file plus an alphabetical insertion in the
  `JacobianChallenge.lean` import manifest.
-/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

/-! ### Chart-pullback congr lemma for `MMeromorphicAt` -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {I : ModelWithCorners ℂ ℂ ℂ}

/-- **Chart-pullback congr.** If `f, g : M → ℂ` agree on a punctured
neighbourhood of `x : M` after pullback through `(chartAt ℂ x).symm`,
then `MMeromorphicAt I` transfers between them. -/
lemma MMeromorphicAt.congr_chartPullback
    {f h : M → ℂ} {x : M}
    (hf : MMeromorphicAt I f x)
    (h_evEq :
      (f ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      (h ∘ (chartAt ℂ x).symm)) :
    MMeromorphicAt I h x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  show MeromorphicAt (h ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  exact hf'.congr h_evEq

/-! ### Per-point meromorphy of `NormFM` from a chart-local product witness -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Per-point meromorphy of `NormFM` from a chart-local product witness.**

Given `y₀ : Y`, a `Finset σ` of indices, a family `F : σ → Y → ℂ` of
factors each `MMeromorphicAt I · y₀`, and a chart-pullback eventual-
equality witness identifying `NormFM f hf hf_nc g` with the `Finset`
product of the `F i` on a punctured neighbourhood of `y₀`, conclude
that `NormFM f hf hf_nc g` is `MMeromorphicAt I · y₀`.

This is the **chart-local product form** of the per-point hypothesis
that `NormFM_mmeromorphicOn_univ_of_pointwise` (ZZ206) takes as input.
The eventual-equality witness is the natural shape that the residual
combinatorial chip (P1.2c/d) will produce; once produced, this lemma
discharges the meromorphy hypothesis cleanly. -/
theorem NormFM_mmeromorphicAt_of_chartLocalProductWitness
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X) (y₀ : Y)
    {σ : Type*} (s : Finset σ) (F : σ → Y → ℂ)
    (hF : ∀ i ∈ s, MMeromorphicAt (𝓘(ℂ, ℂ)) (F i) y₀)
    (h_evEq :
      ((NormFM f hf hf_nc g) ∘ (chartAt ℂ y₀).symm)
        =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)]
      ((fun y : Y => ∏ i ∈ s, F i y) ∘ (chartAt ℂ y₀).symm)) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) y₀ := by
  -- Step 1: the `Finset` product of the `F i` is `MMeromorphicAt y₀`.
  have h_prod :
      MMeromorphicAt (𝓘(ℂ, ℂ)) (fun y : Y => ∏ i ∈ s, F i y) y₀ :=
    mmeromorphicAt_finset_prod (I := 𝓘(ℂ, ℂ)) (x := y₀) s F hF
  -- Step 2: transfer along the eventual-equality witness (in reverse).
  have h_evEq_sym :
      ((fun y : Y => ∏ i ∈ s, F i y) ∘ (chartAt ℂ y₀).symm)
        =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)]
      ((NormFM f hf hf_nc g) ∘ (chartAt ℂ y₀).symm) :=
    h_evEq.symm
  exact MMeromorphicAt.congr_chartPullback (I := 𝓘(ℂ, ℂ))
    (f := fun y : Y => ∏ i ∈ s, F i y)
    (h := NormFM f hf hf_nc g)
    (x := y₀) h_prod h_evEq_sym

/-! ### Global meromorphy of `NormFM` from chart-local product witnesses -/

/-- **Global meromorphy of `NormFM` from chart-local product witnesses.**

Given a chart-local product witness at every `y₀ : Y`, the global
`MMeromorphicOn univ` conclusion follows. Composes with
`NormFM_mmeromorphicAt_of_chartLocalProductWitness` (per-point version)
and `NormFM_mmeromorphicOn_univ_of_pointwise` (ZZ206 conditional global). -/
theorem NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    (h_witnesses :
      ∀ y₀ : Y, ∃ (σ : Type) (s : Finset σ) (F : σ → Y → ℂ),
        (∀ i ∈ s, MMeromorphicAt (𝓘(ℂ, ℂ)) (F i) y₀) ∧
        (((NormFM f hf hf_nc g) ∘ (chartAt ℂ y₀).symm)
          =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)]
        ((fun y : Y => ∏ i ∈ s, F i y) ∘ (chartAt ℂ y₀).symm))) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) Set.univ := by
  apply NormFM_mmeromorphicOn_univ_of_pointwise f hf hf_nc g
  intro y₀
  obtain ⟨σ, s, F, hF, h_evEq⟩ := h_witnesses y₀
  exact NormFM_mmeromorphicAt_of_chartLocalProductWitness
    f hf hf_nc g y₀ s F hF h_evEq

end Manifold
end JacobianChallenge

end
