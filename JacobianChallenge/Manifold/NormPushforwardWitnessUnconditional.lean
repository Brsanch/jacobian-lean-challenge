/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.NormPushforwardGlobal
import JacobianChallenge.Manifold.NormPushforwardGlobalMeromorphy
import JacobianChallenge.Manifold.NormPushforwardManifold

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chart-local product witness for `NormFM`, structural form
(Phase 1 chip P1.2c, ZZ208)

This file ships a **structural intermediate** discharging the universal
hypothesis of `NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses`
(ZZ207) from a packaged "chart-local product data" payload at every
`y₀ : Y`.

The full unconditional discharge of P1.2c requires producing, at every
`y₀ : Y`, the combinatorial object
  fibre-disjointness + per-fibre-point Hurwitz local form + radius
  bookkeeping + product factorization
which is structurally a **single coherent payload**. This file packages
that payload as a `Prop` and proves: payload-at-every-y₀ ⇒ universal
chart-local product witness ⇒ `MMeromorphicOn univ (NormFM …)`.

The remaining residual is then concretely
  ∀ y₀ : Y, `ChartLocalProductWitnessData f hf hf_nc g y₀`
which is a single bundled mathematical claim (rather than the
multi-headed shape of the original universal hypothesis), and can be
discharged by a follow-up chip directly from
`localKFoldMultiplicityOnManifold_genuine_with_radius` +
`analytic_local_normal_form` + `fibres_finite_statement_holds_unconditional`.

## What is shipped

* `ChartLocalProductWitnessData` — bundled `Prop` packaging the
  chart-local product witness at a single `y₀`. This is exactly the
  existential signature that ZZ207's universal hypothesis takes,
  promoted to a named `Prop` to clarify the payload.

* `NormFM_chartLocalProductWitness_holds_of_data` — given the bundled
  data at every `y₀`, the universal hypothesis of ZZ207 holds. This
  is a definitional unfolding (the bundle is the existential).

* `NormFM_mmeromorphicOn_univ_of_chartLocalProductData` — the headline:
  composing the above with ZZ207's
  `NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses` produces
  `MMeromorphicOn (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) Set.univ` from the
  bundled data at every `y₀`.

## Residual: a single concrete chip

The single remaining residual is:

  `∀ y₀ : Y, ChartLocalProductWitnessData f hf hf_nc g y₀`

i.e. produce the chart-local product witness data at every `y₀ : Y`.
The math is: at each `y₀`, the fibre `f⁻¹{y₀}` is finite (by
`fibres_finite_statement_holds_unconditional`); for each `x_i ∈ f⁻¹{y₀}`,
the chart pullback of `f` is in Hurwitz local form `t = w₀ + ψ_i^{k_i}`
near `x_i` (by `analytic_local_normal_form` + the chart-pullback
analyticity); the `localKFoldMultiplicityOnManifold_genuine_with_radius`
witness gives a chart radius and a target neighbourhood on which the
preimages near `x_i` are exactly the `k_i`-th roots of `t - w₀` after
the `ψ_i`-coordinate. Intersecting the per-`x_i` target neighbourhoods
gives a single neighbourhood `V` on which the global fibre decomposes
into the disjoint union of the per-`x_i` local fibres. The product then
factorises across `i`, and each `i`-th factor equals
`normPow (g ∘ ψ_i⁻¹) k_i ((chartAt y₀) y - w₀)`, which is
`MMeromorphicAt y₀` by ZZ205 after a constant translation.

This file frees the next chip from re-shipping the whole stack: it
needs only to discharge the single `ChartLocalProductWitnessData`
predicate at every `y₀`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No `ω` binder anywhere (Lean 4.30 reserved).
* No signature change to any pre-existing definition or theorem.
* Adds one new file plus alphabetical insertion in the import manifest.
-/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-! ### The chart-local product witness data, bundled -/

/-- **Chart-local product witness data at `y₀`.**

This `Prop` packages, at a single `y₀ : Y`, the data needed to feed the
universal hypothesis of `NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses`
(ZZ207).

A witness consists of:
* a `Type σ` and a `Finset σ` indexing the per-fibre-point factors,
* a family `F : σ → Y → ℂ` of factor functions,
* per-factor `MMeromorphicAt y₀` proofs, and
* a chart-pullback eventual-equality witness identifying `NormFM` with
  the `Finset.prod` of the factors on a punctured neighbourhood of `y₀`.

Naming this as a `Prop` clarifies the residual: the next chip's job is
to discharge `∀ y₀, ChartLocalProductWitnessData f hf hf_nc g y₀`,
which is one focused mathematical statement rather than a multi-headed
universal hypothesis. -/
def ChartLocalProductWitnessData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X) (y₀ : Y) : Prop :=
  ∃ (σ : Type) (s : Finset σ) (F : σ → Y → ℂ),
    (∀ i ∈ s, MMeromorphicAt (𝓘(ℂ, ℂ)) (F i) y₀) ∧
    (((NormFM f hf hf_nc g) ∘ (chartAt ℂ y₀).symm)
      =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)]
    ((fun y : Y => ∏ i ∈ s, F i y) ∘ (chartAt ℂ y₀).symm))

/-- **From per-`y₀` data, the universal chart-local product witness.**

Given `ChartLocalProductWitnessData` at every `y₀ : Y`, the universal
hypothesis of `NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses`
(ZZ207) holds. The proof is definitional unfolding of the bundle. -/
theorem NormFM_chartLocalProductWitness_holds_of_data
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    (h_data : ∀ y₀ : Y, ChartLocalProductWitnessData f hf hf_nc g y₀) :
    ∀ y₀ : Y, ∃ (σ : Type) (s : Finset σ) (F : σ → Y → ℂ),
      (∀ i ∈ s, MMeromorphicAt (𝓘(ℂ, ℂ)) (F i) y₀) ∧
      (((NormFM f hf hf_nc g) ∘ (chartAt ℂ y₀).symm)
        =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)]
      ((fun y : Y => ∏ i ∈ s, F i y) ∘ (chartAt ℂ y₀).symm)) := h_data

/-! ### Headline: global meromorphy from packaged chart-local product data -/

/-- **Global meromorphy of `NormFM` from packaged chart-local product
data at every `y₀`.**

Composes
* `NormFM_chartLocalProductWitness_holds_of_data` (this file), and
* `NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses` (ZZ207).

The hypothesis `∀ y₀ : Y, ChartLocalProductWitnessData f hf hf_nc g y₀`
is the residual single-claim chip whose discharge produces the
unconditional `NormFM_mmeromorphicOn_univ` headline. -/
theorem NormFM_mmeromorphicOn_univ_of_chartLocalProductData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    (h_data : ∀ y₀ : Y, ChartLocalProductWitnessData f hf hf_nc g y₀) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) Set.univ :=
  NormFM_mmeromorphicOn_univ_of_chartLocalProductWitnesses
    f hf hf_nc g
    (NormFM_chartLocalProductWitness_holds_of_data f hf hf_nc g h_data)

/-! ### A trivial `MMeromorphicAt` factor: the constant-`1` factor

This factor is `MMeromorphicAt y₀` and is used in degenerate witness
constructions (e.g. when the empty fibre case is allowed structurally,
the chart-local product is the empty product `1`). -/

/-- The constant-`1` function is `MMeromorphicAt I y₀` on any charted
space. -/
lemma mmeromorphicAt_const_one
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {I : ModelWithCorners ℂ ℂ ℂ} (x : M) :
    MMeromorphicAt I (fun _ : M => (1 : ℂ)) x :=
  MMeromorphicAt.const 1

end Manifold
end JacobianChallenge

end
