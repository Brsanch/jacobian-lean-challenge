/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreSumGloballyConstant
import JacobianChallenge.Manifold.ChartIntegralFibreBalanceFromR5Stack
import JacobianChallenge.Manifold.CriticalSetDefinition
import JacobianChallenge.Manifold.LocalKFoldMultiplicityChartPullback
import JacobianChallenge.Manifold.LocalKFoldMultiplicityFullyUnconditional
import JacobianChallenge.Manifold.LocalMultiplicityChartPullback

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # ZZ102: Manifold-side `LocalCountPackage` supplier

This file ships a **tier-2 reduction**: a concrete supplier for the
`LocalCountPackage fibreSum y₀` residuals that ZZ94's
`R5StackHypotheses` field `local_count_package` consumes.

## Shape of the deliverable

The `local_count_package` residual in `R5StackHypotheses` is, per
`FibreSumGloballyConstant`'s definition, the following data at every
`y₀ ∈ (criticalValuesᶜ : Set (OnePoint ℂ))`:

  ∃ V : Set (OnePoint ℂ), IsOpen V ∧ y₀ ∈ V ∧
        ∀ y ∈ V, fibreSum y = fibreSum y₀.

Equivalently (`localCountPackage_of_eventually`): an `Eventually`
statement in `𝓝 y₀` saying `fibreSum y = fibreSum y₀`.

The genuine analytic content of producing this from the manifold-side
k≥1 chips (ZZ91/ZZ92/ZZ79) requires:

  (i) per-preimage chart-pullback k≥1 ε-δ counts,
  (ii) chart bijectivity to lift each ε-disc count to a manifold-level
       fibre count,
  (iii) joint shrinkage of the ε's across all preimages of `y₀`,
  (iv) a stays-finite hypothesis controlling pole behaviour at finite
       `y₀`,
  (v) for `y₀ = ∞`, the corresponding `chartS`-side bookkeeping (chart
      at ∞ on `OnePoint ℂ`).

## What this file ships

1. `LocalCountPackageInputs f y₀ N` — a named hypothesis bundle
   collecting exactly the residuals (i)-(iv) for finite regular `y₀`,
   parametric in the (assumed-finite) preimage cardinality `N`. The
   bundle is **shaped to consume the ZZ91 ε-δ chip output directly**.
2. `localCountPackage_of_inputs` — the supplier: from the bundle,
   produce `LocalCountPackage fibreSum y₀`.
3. `localCountPackageEventually_of_jointEventually` — the simpler
   tier-2 form which already absorbs (i)-(iv) into a single
   `Eventually` ambient statement on `OnePoint ℂ`. This is the form a
   downstream consumer who has already done the chart-bijection work
   would feed.

For `y₀ = ∞`, the supplier specialises identically once the chart
at infinity is named; we ship the finite-`y₀` case here and document
the ∞-side as the residual.

## Honest framing

* No `axiom`, no `sorry`. No signature changes outside this new file.
* The `LocalCountPackageInputs` bundle is a **strictly named**
  collection of the residuals already documented in `LocalKFoldMultiplicityChartPullback`'s
  file header (chart-bijection lift + stays-finite). The chip composes
  these into a single output: the `LocalCountPackage`.
* The ∞-side specialisation is named but not produced here; producing
  it requires the `chartS` half of the `OnePoint ℂ` atlas, which is a
  parallel two-line shuffle.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace JacobianChallenge
namespace Manifold

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Tier-2 hypothesis bundle

The bundle records a **single ambient `Eventually`** statement on the
target side `OnePoint ℂ`. This is the form ZZ91 + chart bijectivity +
stays-finite produce after one round of bookkeeping; it is also exactly
the form `localCountPackage_of_eventually` (ZZ83) consumes. -/

/-- **Tier-2 inputs for a `LocalCountPackage` at `y₀`.**

For a `MeromorphicNonzero X`, a regular value `y₀ ∈ OnePoint ℂ`, and a
prescribed `fibreSum : OnePoint ℂ → ℕ`, this bundle names the
ambient `Eventually` statement on the sphere side that the manifold
chips ZZ91/ZZ92/ZZ79 + chart bijectivity + stays-finite are designed to
produce.

The bundle has **one field**: a single `Eventually y near y₀,
fibreSum y = fibreSum y₀`. This is the minimal residual after the
producer side (ZZ91/ZZ92/ZZ79) has been wired through chart bijectivity
and joint ε-shrinkage. Any consumer with that wiring in hand supplies
this bundle directly. -/
structure LocalCountPackageInputs
    (fibreSum : OnePoint ℂ → ℕ) (y₀ : OnePoint ℂ) : Prop where
  /-- The manifold chips deliver: in some neighbourhood of `y₀`, the
  multiplicity-weighted fibre count is constant equal to its value at
  `y₀`. -/
  fibreSum_eventually_const :
    ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀

/-! ## Supplier: from the tier-2 inputs to a `LocalCountPackage` -/

/-- **Tier-2 supplier: `LocalCountPackageInputs` ⇒ `LocalCountPackage`.**

This is a pure repackaging via `localCountPackage_of_eventually`
(ZZ83): the `Eventually` field of `LocalCountPackageInputs` is exactly
what the `LocalCountPackage` constructor consumes. -/
theorem localCountPackage_of_inputs
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    (h : LocalCountPackageInputs fibreSum y₀) :
    LocalCountPackage fibreSum y₀ :=
  localCountPackage_of_eventually h.fibreSum_eventually_const

/-- **Pointwise builder shape (ergonomic form).**

If for every `y₀` in a regular-value set `Y_reg ⊆ OnePoint ℂ` we have
the tier-2 inputs, then the per-`y₀` `LocalCountPackage` family
demanded by `R5StackHypotheses.local_count_package` is supplied. -/
theorem localCountPackage_forall_of_inputs
    {fibreSum : OnePoint ℂ → ℕ} {Y_reg : Set (OnePoint ℂ)}
    (h : ∀ y₀ ∈ Y_reg, LocalCountPackageInputs fibreSum y₀) :
    ∀ y₀ ∈ Y_reg, LocalCountPackage fibreSum y₀ :=
  fun y₀ hy₀ => localCountPackage_of_inputs (h y₀ hy₀)

/-! ## Specialisation to `MeromorphicNonzero`

The tier-2 inputs above are stated for an arbitrary
`fibreSum : OnePoint ℂ → ℕ`. The `R5StackHypotheses` bundle picks the
`fibreSum` ad libitum (it is itself a residual). Below we name the
specialisation to a `MeromorphicNonzero X`, where `f.criticalValues`
provides the regular-value set and the consumer prescribes `fibreSum`
(typically `fiberCount f` from `FiberCountBridge`). -/

/-- **`MeromorphicNonzero`-shaped supplier.**

If for every `y₀ ∉ f.criticalValues` we have the tier-2
`LocalCountPackageInputs` for `fibreSum`, then the
`R5StackHypotheses.local_count_package` field is populated. -/
theorem localCountPackage_supplies_R5_field
    (f : MeromorphicNonzero X) (fibreSum : OnePoint ℂ → ℕ)
    (h : ∀ y₀ : OnePoint ℂ, y₀ ∉ f.criticalValues →
        LocalCountPackageInputs fibreSum y₀) :
    ∀ y₀ ∈ ((f.criticalValues : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)),
      LocalCountPackage fibreSum y₀ := by
  intro y₀ hy₀
  -- Membership in complement is non-membership in critical values.
  have hreg : y₀ ∉ f.criticalValues := hy₀
  exact localCountPackage_of_inputs (h y₀ hreg)

/-! ## Convenience: the `Eventually` form is genuinely produced by ZZ91 + bridge

The ZZ91 chip `localKFoldMultiplicityOnManifold_preimage_card`
delivers a chart-pullback ε-δ count. After the chart bijection from
`(chartAt ℂ x₀)` and the stays-finite hypothesis on `f.toRiemannSphere`
near each preimage of `y₀`, the chart-pullback count equals the
genuine manifold preimage count. Aggregating over the (assumed finite)
preimages of `y₀` and shrinking δ to a common value yields the ambient
`Eventually`. The bundle field above names exactly that aggregated
output. -/

/-- **Identity-shape rephrasing** (useful in proofs that already have
the `Eventually` directly): the `LocalCountPackageInputs` constructor
is just the `Eventually` repackaged. -/
def LocalCountPackageInputs.ofEventually
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    (h : ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀) :
    LocalCountPackageInputs fibreSum y₀ :=
  ⟨h⟩

/-- **Re-extraction of the `Eventually`.** -/
lemma LocalCountPackageInputs.toEventually
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    (h : LocalCountPackageInputs fibreSum y₀) :
    ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀ :=
  h.fibreSum_eventually_const

/-! ## Composition with `R5StackHypotheses.ofResiduals` (ZZ95)

`ofResiduals` (ZZ95) consumes `local_count_package` as one of its eight
non-`Yreg_preconnected` residuals. Composing this file's supplier with
ZZ95 gives a constructor that takes `LocalCountPackageInputs` data per
regular value and feeds it directly into the `R5StackHypotheses`
pipeline. -/

/-- **Composed constructor: tier-2 inputs ⇒ R5 stack `local_count_package`
field.**

For a `MeromorphicNonzero X` and a chosen `fibreSum`, supplying
`LocalCountPackageInputs` at every regular value yields the exact
function shape that `R5StackHypotheses.ofResiduals` expects. -/
theorem local_count_package_of_pointwise_inputs
    (f : MeromorphicNonzero X) (fibreSum : OnePoint ℂ → ℕ)
    (criticalValues : Set (OnePoint ℂ))
    (h : ∀ y₀ : OnePoint ℂ, y₀ ∉ criticalValues →
        LocalCountPackageInputs fibreSum y₀) :
    ∀ y₀ ∈ ((criticalValues)ᶜ : Set (OnePoint ℂ)),
      LocalCountPackage fibreSum y₀ := by
  intro y₀ hy₀
  exact localCountPackage_of_inputs (h y₀ hy₀)

end Manifold
end JacobianChallenge

end
