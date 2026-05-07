/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalMultiplicityChartPullback
import JacobianChallenge.Manifold.LocalMultiplicityInvariance
import JacobianChallenge.Manifold.LocalKFoldMultiplicity
import JacobianChallenge.Manifold.CriticalSetDiscrete
import JacobianChallenge.Manifold.PoleExtensionFibres
import Mathlib.Topology.LocallyConstant.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Global constancy of the multiplicity-weighted fibre count

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold
`X`, the pole-extension `f̃ : X → RiemannSphere` is a finite branched
cover. On the **regular-value set** `Y_reg ⊆ RiemannSphere` (the open
dense set of values not attained at any critical point and at which the
fibre is finite) the multiplicity-weighted fibre count

  `fibreSum f̃ y := ∑_{x ∈ f̃ ⁻¹' {y}} localMult f̃ x`

is **locally constant**. On a connected `Y_reg` it is then globally
constant — the topological/algebraic statement of the degree of a
branched cover.

## Status — Tier-2 reduction

Following the same pattern as ZZ79
(`LocalMultiplicityChartPullback.lean`), we ship the result as a
**hypothesis-parameterised reduction**: the user supplies

* `localMult : X → ℕ`         — the local-multiplicity function
* `fibreSum : RiemannSphere → ℕ` — the fibre-sum function
* `Y_reg   : Set RiemannSphere`  — the regular-value set

together with the **local-count package** that ZZ79 provides at every
preimage of every regular value (`LocalCountAtPreimage`), and we
conclude:

1. `fibreSum_isLocallyConstant_on_Y_reg` — local constancy on `Y_reg` in
   the subtype topology.
2. `fibreSum_eq_of_isPreconnected` — for connected `Y_reg`, the fibre-sum
   takes the same value at any two regular values.

The argument below is **purely topological**: it only uses
`IsLocallyConstant.apply_eq_of_isPreconnected` after we package the
ZZ79 ε-δ data into a "constant on a punctured neighbourhood" statement.

The genuine analytic content — that for `y₀ ∈ Y_reg`, the chart-pullback
preimage count near every `x ∈ f̃ ⁻¹' {y₀}` summed over `x` equals
`fibreSum f̃ y₀` and is independent of the value `y` near `y₀` — is
expressed by the `LocalCountPackage` hypothesis bundle. ZZ79
(`localMultiplicityOnManifold_preimage_card_one`) is the per-preimage
input to this bundle in the `k = 1` case; the general (`k ≥ 1`)
chart-pullback ε-δ count comes from
`localKFoldMultiplicity_preimage_card_of_substitution_one` (ZZ75) once
ZZ79 is repackaged for `k ≥ 1`.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace JacobianChallenge
namespace Manifold

universe u v

/-! ## Local-count package

A `LocalCountPackage` for `f̃ : X → Y` at a value `y₀ : Y` asserts that on
some open neighbourhood `V` of `y₀`, the multiplicity-weighted fibre-count
function `fibreSum` is constant. This is the conclusion ZZ79 delivers
chart-locally; we take it here as a hypothesis (one bundle per
`y₀ ∈ Y_reg`) so the global theorem can be discharged purely
topologically. -/
structure LocalCountPackage
    {Y : Type v} [TopologicalSpace Y]
    (fibreSum : Y → ℕ) (y₀ : Y) : Prop where
  /-- Some open neighbourhood `V` of `y₀` on which `fibreSum` is constant. -/
  exists_const_nhd :
    ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V, fibreSum y = fibreSum y₀

namespace LocalCountPackage

variable {Y : Type v} [TopologicalSpace Y]

/-- A `LocalCountPackage` at `y₀` immediately gives an open neighbourhood
witnessing local constancy. -/
lemma eventually_eq {fibreSum : Y → ℕ} {y₀ : Y}
    (h : LocalCountPackage fibreSum y₀) :
    ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀ := by
  obtain ⟨V, hV_open, hy₀, hconst⟩ := h.exists_const_nhd
  exact (hV_open.mem_nhds hy₀).mono (fun y hy => hconst y hy)

end LocalCountPackage

/-! ## Local constancy on `Y_reg`

If `fibreSum` admits a `LocalCountPackage` at every point of a set
`Y_reg ⊆ Y`, then the restriction of `fibreSum` to `Y_reg` is locally
constant in the subspace topology. -/

variable {Y : Type v} [TopologicalSpace Y]

/-- **Local constancy on the regular-value set.**

If for every `y₀ ∈ Y_reg` the function `fibreSum` admits a
`LocalCountPackage`, then the restriction of `fibreSum` to the subtype
`Y_reg` is `IsLocallyConstant`.

This is the topological packaging step: the ZZ79 ε-δ chart-pullback
content goes into building each `LocalCountPackage` at the producer
side; here we only assemble the local-constancy property in the
subspace topology. -/
theorem fibreSum_isLocallyConstant_on_Y_reg
    (fibreSum : Y → ℕ) (Y_reg : Set Y)
    (h_pkg : ∀ y₀ ∈ Y_reg, LocalCountPackage fibreSum y₀) :
    IsLocallyConstant (fun y : Y_reg => fibreSum y.val) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  -- Pull the ambient `eventually` along the subtype inclusion.
  have h_amb : ∀ᶠ z in 𝓝 (y.val), fibreSum z = fibreSum y.val :=
    (h_pkg y.val y.property).eventually_eq
  -- Subtype-topology pullback of an ambient `eventually`.
  have h_cont : Continuous (fun z : Y_reg => z.val) := continuous_subtype_val
  have := h_cont.continuousAt (x := y) h_amb
  -- `ContinuousAt` on a constant target gives the eventually-equal we need.
  exact this

/-- **Globalisation by preconnectedness.**

If `Y_reg` is preconnected (as a subspace) and `fibreSum` is locally
constant on it, then `fibreSum` takes the same value at any two regular
values.

Specialises `IsLocallyConstant.apply_eq_of_isPreconnected` to the
subtype `Y_reg`. -/
theorem fibreSum_eq_of_isPreconnected
    (fibreSum : Y → ℕ) (Y_reg : Set Y)
    (h_pkg : ∀ y₀ ∈ Y_reg, LocalCountPackage fibreSum y₀)
    (h_conn : IsPreconnected (Set.univ : Set Y_reg))
    {y₁ y₂ : Y} (hy₁ : y₁ ∈ Y_reg) (hy₂ : y₂ ∈ Y_reg) :
    fibreSum y₁ = fibreSum y₂ := by
  have h_lc : IsLocallyConstant (fun y : Y_reg => fibreSum y.val) :=
    fibreSum_isLocallyConstant_on_Y_reg fibreSum Y_reg h_pkg
  have h := h_lc.apply_eq_of_isPreconnected h_conn
    (Set.mem_univ (⟨y₁, hy₁⟩ : Y_reg))
    (Set.mem_univ (⟨y₂, hy₂⟩ : Y_reg))
  simpa using h

/-! ## ZZ79-driven `LocalCountPackage` builders

The producer side: convert the ε-δ chart-pullback count of ZZ79 into a
`LocalCountPackage`. We provide a one-step bridge that consumes a
*manifold-level* statement of the form ZZ79 conjuncted across all
preimages of a regular value. The bridge is shaped to consume the
existing chart-pullback bundle without re-deriving the chart bijectivity
content here.

This is the tier-2 hand-off: callers who already have ZZ79's ε-δ count
plus a chart-bijection finiteness argument supply a single function
`localCount_const : ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀` and obtain
the package automatically. -/

/-- **Build `LocalCountPackage` from an `eventually` statement.** This is
the convenient form for callers who have already pushed ZZ79's ε-δ count
through chart bijectivity to obtain an ambient `eventually` equality. -/
theorem localCountPackage_of_eventually
    {fibreSum : Y → ℕ} {y₀ : Y}
    (h : ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀) :
    LocalCountPackage fibreSum y₀ := by
  rcases (mem_nhds_iff.mp h) with ⟨V, hV_sub, hV_open, hy₀⟩
  exact ⟨V, hV_open, hy₀, hV_sub⟩

/-! ## Headline corollary

Combining the two halves: if every regular value carries an `eventually`
constancy statement and `Y_reg` is preconnected, then `fibreSum` is
globally constant on `Y_reg`. -/

/-- **Global constancy of the multiplicity-weighted fibre count.**

Tier-2 reduction: assuming the `eventually`-form chart-pullback count at
every regular value (the manifold-level upgrade of ZZ79's ε-δ result, via
chart bijectivity), and preconnectedness of `Y_reg`, the function
`fibreSum` is constant on `Y_reg`. -/
theorem fibreSum_globallyConstant_on_Y_reg
    (fibreSum : Y → ℕ) (Y_reg : Set Y)
    (h_eventually : ∀ y₀ ∈ Y_reg, ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀)
    (h_conn : IsPreconnected (Set.univ : Set Y_reg))
    {y₁ y₂ : Y} (hy₁ : y₁ ∈ Y_reg) (hy₂ : y₂ ∈ Y_reg) :
    fibreSum y₁ = fibreSum y₂ :=
  fibreSum_eq_of_isPreconnected fibreSum Y_reg
    (fun y₀ hy₀ => localCountPackage_of_eventually (h_eventually y₀ hy₀))
    h_conn hy₁ hy₂

end Manifold
end JacobianChallenge

end

end
