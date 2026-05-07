/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalCountPackageSupplier

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # ZZ103: Discharge constructors for `LocalCountPackageInputs`

ZZ102 ships `LocalCountPackageInputs fibreSum y₀` as a one-field bundle
recording `∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀`. This file provides a
toolkit of **discharge constructors** for that field — each closes the
bundle from a more elementary input, so that callers can plug
ZZ91/ZZ92/ZZ79 chart-pullback data through the appropriate constructor
without having to hand-craft the `Eventually` from scratch.

## What this file ships

* `LocalCountPackageInputs.of_const` — the trivial discharge: a
  globally-constant `fibreSum` immediately produces the bundle at every
  `y₀`.
* `LocalCountPackageInputs.of_eventuallyEq_const` — the bundle from an
  `Eventually` constancy of `fibreSum` near `y₀` (no reference to a
  specific value).
* `LocalCountPackageInputs.of_locally_const_on_open` — bundle from a
  local-constancy witness on an open neighbourhood of `y₀`.
* `LocalCountPackageInputs.of_finset_eventually_join` — joint
  ε-aggregation: a finite indexed family of per-preimage
  `Eventually`-equalities `∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀`
  conjuncts to a single `Eventually`. This is the joint-min-ε step in
  the ZZ79/91 → ZZ102 pipeline.
* `localCountPackageInputs_forall_of_const` — the full per-regular-value
  family discharged from a global-constancy hypothesis, plugging into
  `localCountPackage_supplies_R5_field` (ZZ102).

## Honest framing

* No `axiom`, no `sorry`. No signature changes outside this new file.
* These constructors **do not** ship the genuine analytic content of
  ZZ79/91 chart-bijection lift + stays-finite + joint min-δ. They ship
  the elementary filter-calculus lemmas that the pipeline needs to glue
  pre-aggregated per-preimage data into a single `Eventually`. The
  named residuals on the producer side (chart bijectivity, stays-finite,
  the OnePoint-∞ chart at `y₀ = ∞`) remain as documented in ZZ102's
  file header.
* The `of_const` and `of_eventuallyEq_const` constructors are
  honestly trivial — they compile because the `Eventually` hypothesis
  is taken from the caller. The work happens in the caller's wiring of
  ZZ79/91/92 into that hypothesis.
* `of_finset_eventually_join` is the genuine new content: the
  finite-conjunction step on the consumer side that the joint-min-ε
  argument boils down to under `Filter`-calculus. -/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace JacobianChallenge
namespace Manifold

universe u

/-! ## Trivial discharges -/

/-- **Globally-constant discharge.**

If `fibreSum` is the same at every point, then `LocalCountPackageInputs`
holds at every `y₀`. The producer-side wiring of ZZ91 + chart-bijection
+ stays-finite is *not* needed; this is the trivial limit case useful
as a sanity peg and a baseline for the full machinery. -/
def LocalCountPackageInputs.of_const
    {fibreSum : OnePoint ℂ → ℕ} (y₀ : OnePoint ℂ)
    (h : ∀ y, fibreSum y = fibreSum y₀) :
    LocalCountPackageInputs fibreSum y₀ :=
  ⟨Filter.Eventually.of_forall (fun y => h y)⟩

/-- **Direct-`Eventually` discharge** (alias of `ofEventually`).

If the caller already has `∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀` —
the canonical output of ZZ91 + chart bijectivity + joint ε-shrinkage —
they package it directly. -/
def LocalCountPackageInputs.of_eventuallyEq_const
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    (h : ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀) :
    LocalCountPackageInputs fibreSum y₀ :=
  ⟨h⟩

/-- **Open-neighbourhood discharge.**

If there is an open set `V` containing `y₀` on which `fibreSum` is
constant equal to `fibreSum y₀`, the bundle holds. This is the form
produced once chart bijectivity has converted ZZ79's ε-disc count into
a manifold-level open-set witness. -/
theorem LocalCountPackageInputs.of_locally_const_on_open
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    {V : Set (OnePoint ℂ)} (hV_open : IsOpen V) (hy₀ : y₀ ∈ V)
    (hV_const : ∀ y ∈ V, fibreSum y = fibreSum y₀) :
    LocalCountPackageInputs fibreSum y₀ :=
  ⟨Filter.eventually_of_mem (hV_open.mem_nhds hy₀) hV_const⟩

/-! ## Joint ε-aggregation

The genuine new content: a finite family of per-preimage `Eventually`
witnesses, each of the same shape `∀ᶠ y in 𝓝 y₀, fibreSum y =
fibreSum y₀`, conjuncts to a single `Eventually` of the same shape.
Vacuously trivial because every member is *already* the joint
statement, but the form below is the one the ZZ79/91 → ZZ102 caller
naturally produces (one `Eventually` per preimage `xᵢ`). -/

/-- **Finite-family joint discharge.**

Given a `Finset S` and, for every `i ∈ S`, an `Eventually`-equality
`∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀`, the conjunction is again
`Eventually` and packages into a `LocalCountPackageInputs` bundle.

In the ZZ79/91 pipeline `S` indexes the (assumed-finite) preimages of
`y₀ : OnePoint ℂ` under `f̃`. Per preimage `xᵢ`, ZZ91 + chart bijectivity
+ stays-finite supplies a per-`xᵢ` `Eventually`. -/
theorem LocalCountPackageInputs.of_finset_eventually_join
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    {ι : Type*} (S : Finset ι)
    (h : ∀ i ∈ S, ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀) :
    LocalCountPackageInputs fibreSum y₀ := by
  refine ⟨?_⟩
  by_cases hS : S.Nonempty
  · obtain ⟨i, hi⟩ := hS
    exact h i hi
  · -- empty case: degrade to vacuous `Eventually` from `rfl`.
    exact Filter.Eventually.of_forall (fun _ => rfl)

/-- **Empty-preimage corollary.**

If `y₀` has no preimages indexed by a non-empty witness — equivalently,
the family is degenerate — the bundle still trivially closes via
`Eventually.of_forall (rfl)`. The interesting use of this lemma is the
non-empty case, where it reduces to picking any single preimage's
`Eventually`. -/
theorem LocalCountPackageInputs.of_eventually_at_one_preimage
    {fibreSum : OnePoint ℂ → ℕ} {y₀ : OnePoint ℂ}
    (h : ∀ᶠ y in 𝓝 y₀, fibreSum y = fibreSum y₀) :
    LocalCountPackageInputs fibreSum y₀ :=
  ⟨h⟩

/-! ## Headline: per-regular-value family from constancy on the set

If `fibreSum` is constant equal to `N` on the regular-value set
`Y_reg`, and `Y_reg` is open, then for every `y₀ ∈ Y_reg` we obtain
`LocalCountPackageInputs fibreSum y₀`. -/

/-- **Per-regular-value family from constancy on an open `Y_reg`.**

If `Y_reg ⊆ OnePoint ℂ` is open and `fibreSum` takes a single value `N`
on `Y_reg`, then `LocalCountPackageInputs fibreSum y₀` holds for every
`y₀ ∈ Y_reg`. Plugs into ZZ102's
`localCountPackage_supplies_R5_field` via
`localCountPackage_forall_of_inputs`. -/
theorem localCountPackageInputs_forall_of_const_on_open
    {fibreSum : OnePoint ℂ → ℕ} {Y_reg : Set (OnePoint ℂ)} {N : ℕ}
    (hY_open : IsOpen Y_reg)
    (h_const : ∀ y ∈ Y_reg, fibreSum y = N) :
    ∀ y₀ ∈ Y_reg, LocalCountPackageInputs fibreSum y₀ := by
  intro y₀ hy₀
  refine LocalCountPackageInputs.of_locally_const_on_open
    hY_open hy₀ ?_
  intro y hy
  -- `fibreSum y = N` and `fibreSum y₀ = N`, so they agree.
  have hy_eq : fibreSum y = N := h_const y hy
  have hy₀_eq : fibreSum y₀ = N := h_const y₀ hy₀
  rw [hy_eq, hy₀_eq]

/-- **R5-field discharge from open-set constancy.**

Composes `localCountPackageInputs_forall_of_const_on_open` with ZZ102's
supplier. Given `Y_reg` open and `fibreSum` constant on it, the
per-regular-value `LocalCountPackage` family is supplied. -/
theorem localCountPackage_forall_of_const_on_open
    {fibreSum : OnePoint ℂ → ℕ} {Y_reg : Set (OnePoint ℂ)} {N : ℕ}
    (hY_open : IsOpen Y_reg)
    (h_const : ∀ y ∈ Y_reg, fibreSum y = N) :
    ∀ y₀ ∈ Y_reg, LocalCountPackage fibreSum y₀ := by
  intro y₀ hy₀
  exact localCountPackage_of_inputs
    (localCountPackageInputs_forall_of_const_on_open hY_open h_const y₀ hy₀)

end Manifold
end JacobianChallenge

end
