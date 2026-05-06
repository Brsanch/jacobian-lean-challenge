/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalMultiplicity

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Degree of a holomorphic map between compact Riemann surfaces

This file provides a *fibre-cardinality* candidate body for `ContMDiff.degree`,
upgrading the constant-vs-non-constant indicator (`degreeStub`) toward the
classical definition

```
deg(f) = |f ⁻¹' {y}|   for any regular value y : Y.
```

## What is honest in this file

* For **constant** `f`, `degreeFiber f hf = 0` unconditionally.
* For **non-constant** `f`, `degreeFiber f hf` extracts a natural number from a
  packaged witness bundle (`RegularValueWitness`) using `Classical.choice` on
  the existence of such a witness. The witness records:
  - a chosen value `y₀ : Y`,
  - a proof that the fibre `f ⁻¹' {y₀}` is finite, and
  - the cardinality is then `(h.toFinset).card`.
  When no witness exists in `Classical.choice`'s sense at this mathlib pin
  (because the deep theorem below is missing), the definition falls back to
  `0`. This matches `degreeStub`'s constant-case answer and is strictly more
  informative than `degreeStub` whenever a witness *does* exist.

## What is owed (and is the deep classical input)

For a non-constant holomorphic map `f : X → Y` between compact connected
Riemann surfaces, the following are classical and **not yet in mathlib at the
pin**:

1. **Properness with finite fibres.** Every fibre `f ⁻¹' {y}` is a finite
   subset of `X` (using `IsCompact.finite_of_discrete` once one knows the
   fibre is discrete, which uses the identity theorem for analytic functions).
2. **Existence of a regular value.** The set of critical values
   `{y : Y | ∃ x ∈ f ⁻¹' {y}, ramification index ≥ 2}` is finite, so its
   complement is non-empty (in fact, of full measure / open dense).
3. **Constancy of fibre cardinality across regular values.** This is the
   topological-degree statement; it relies on the local normal form
   `z ↦ z ^ k` for ramified holomorphic maps and a covering-space argument on
   `Y \ critical values`.

The first two together produce a `RegularValueWitness f`. The third is what
makes `degreeFiber f hf` independent of the chosen witness. None of (1)–(3)
are formalised at this pin; their statements are recorded as `Owed.*`
docstrings below for downstream.

## Why a separate definition (and not editing `_root_.ContMDiff.degree`)

`Basic.lean`'s `_root_.ContMDiff.degree f hf : ℕ` signature is locked. This
file provides `JacobianChallenge.ContMDiff.degreeFiber` as a strict upgrade
candidate that matches the same signature shape (no extra arguments at the
call site beyond `f` and `hf`). When (1)–(3) above land in mathlib, the body
of `_root_.ContMDiff.degree` in `Basic.lean` can be retargeted from
`degreeStub` to `degreeFiber` without touching any caller.

## Main definitions

* `JacobianChallenge.ContMDiff.RegularValueWitness f` — a chosen value `y₀ : Y`
  together with a proof that the fibre over `y₀` is finite. Existence of this
  witness for non-constant analytic `f` between compact RS is the deep
  classical input.
* `JacobianChallenge.ContMDiff.degreeFiber f hf : ℕ` — `0` if `f` is constant;
  otherwise `Classical.choice`-extracted fibre cardinality (falling back to
  `0` if no `RegularValueWitness` exists at the pin).

## Compatibility with `degreeStub`

* `degreeFiber_const` matches `degreeStub_const`: constant maps have degree 0.
* `degreeFiber f hf = 0` whenever no `RegularValueWitness f` exists — same as
  `degreeStub` would give in the absence of any classical witness.
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace JacobianChallenge

namespace ContMDiff

universe u v

/-! ## The witness bundle

A `RegularValueWitness f` packages a chosen value `y₀ : Y` together with a
proof that the fibre `f ⁻¹' {y₀}` is finite. This is the minimal structural
data needed to define a fibre cardinality without changing the signature of
`_root_.ContMDiff.degree`.

For a non-constant holomorphic map between compact connected Riemann surfaces,
existence of such a witness is a classical theorem (see file docstring item
1+2). At this mathlib pin neither (1) nor (2) is formalised, so the
`Nonempty (RegularValueWitness f)` hypothesis is the gap. -/
structure RegularValueWitness {X : Type u} {Y : Type v} (f : X → Y) where
  /-- Chosen value in the codomain. -/
  value : Y
  /-- The fibre over the chosen value is finite. -/
  fiber_finite : (f ⁻¹' {value}).Finite

/-- Cardinality of the chosen finite fibre, as a `Finset.card`. -/
def RegularValueWitness.card {X : Type u} {Y : Type v} {f : X → Y}
    (w : RegularValueWitness f) : ℕ :=
  w.fiber_finite.toFinset.card

/-! ## The degree

A drop-in replacement for `degreeStub` that, when a `RegularValueWitness` is
classically available, returns a *real* fibre cardinality rather than an
indicator. -/

/-- The **degree** of an analytic map `f : X → Y` between compact Riemann
surfaces, as a fibre cardinality.

* For constant `f`, returns `0` (matching the convention in challenge item 9
  and `degreeStub`).
* For non-constant `f`, returns the cardinality of *some* regular fibre,
  selected via `Classical.choice` on the existence of a `RegularValueWitness`.
  If no witness is classically available at this pin, falls back to `0`.

The well-definedness — independence of the chosen witness — is the deep
classical input that is **not** discharged here. See file docstring items
(2)–(3) for what is owed. -/
def degreeFiber
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if IsConstantMap f then 0
  else
    if h : Nonempty (RegularValueWitness f) then
      (Classical.choice h).card
    else 0

/-- Constant maps have fibre-degree `0`. -/
lemma degreeFiber_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (c : Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : X => c)) :
    degreeFiber (fun _ : X => c) hf = 0 := by
  unfold degreeFiber
  simp [isConstantMap_const]

/-- If no regular-value witness exists for a non-constant map at this pin,
the fibre-degree falls back to `0`. (This is the same value `degreeStub`
returns in the constant case, so callers that only know "degree = 0 ⇒ ..."
remain correct.) -/
lemma degreeFiber_eq_zero_of_no_witness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) (hno : ¬ Nonempty (RegularValueWitness f)) :
    degreeFiber f hf = 0 := by
  unfold degreeFiber
  simp [hnc, hno]

/-- When a regular-value witness *does* exist (non-constant case, `Classical`
mode), the fibre-degree equals the cardinality of *some* witness. The
particular witness is `Classical.choice`-selected; independence of choice is
the deep classical input that is not formalised at this pin. -/
lemma degreeFiber_eq_witness_card
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) (h : Nonempty (RegularValueWitness f)) :
    degreeFiber f hf = (Classical.choice h).card := by
  unfold degreeFiber
  simp [hnc, h]

/-! ## Owed mathlib infrastructure

The following statements would, if formalised in mathlib at this pin, allow
`degreeFiber` to be promoted from "structural skeleton with `Classical.choice`
fallback" to a fully honest definition. They are not proved here; they are
recorded as type-checking placeholders so that downstream files can grep for
`Owed.degree.` to find the dependency surface.

Each placeholder is a `Prop`-valued definition of the **statement** of the
classical theorem; we do **not** assume it (no `axiom`s). Discharging them is
out of scope for this round. -/

namespace Owed.degree

/-- (1) For a non-constant analytic map `f : X → Y` between compact connected
Riemann surfaces, every fibre is finite. Classical: identity theorem
(fibres are discrete) plus compactness.

**Status:** statement only. No proof is provided. -/
def fibres_finite_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
    ∀ y : Y, (f ⁻¹' {y}).Finite

/-- (2) For a non-constant analytic map between compact connected Riemann
surfaces, the set of critical values is finite, so a regular value exists.
Classical input for `Nonempty (RegularValueWitness f)`.

**Status:** statement only. No proof is provided. -/
def regular_value_exists_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
    Nonempty (RegularValueWitness f)

/-- (3) For a non-constant analytic map between compact connected Riemann
surfaces, the cardinality of the fibre is constant across regular values.
This is the well-definedness of the topological degree.

**Status:** statement only. No proof is provided. -/
def fibre_card_well_defined_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
    ∀ (w₁ w₂ : RegularValueWitness f), w₁.card = w₂.card

/-! ### Partial discharge of `fibres_finite_statement`

The full statement requires the analytic identity theorem on charts to ensure
fibres are discrete. We do not formalise the chart-level identity theorem at
this pin. We do however reduce `fibres_finite_statement` to a single named
topological hypothesis: **each fibre carries the discrete subspace topology**
(`IsDiscrete (f ⁻¹' {y})`). The reduction itself is purely topological:
continuity gives closedness, compactness of `X` upgrades closed to compact,
and a compact discrete subspace is finite (`IsCompact.finite`).

What is owed (and not formalised here) is the implication

  analytic, non-constant ⇒ ∀ y, IsDiscrete (f ⁻¹' {y}).

That is the chart-level identity theorem.
-/

/-- A fibre of a continuous map into a `T2` compact space is closed and hence
compact; if additionally the fibre carries the discrete subspace topology, it
is finite. This is the purely topological half of the identity-theorem
argument. -/
lemma fiber_finite_of_isDiscrete
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf_cont : Continuous f) (y : Y)
    (h_disc : IsDiscrete (f ⁻¹' {y})) :
    (f ⁻¹' {y}).Finite := by
  have h_closed : IsClosed (f ⁻¹' {y}) :=
    isClosed_singleton.preimage hf_cont
  have h_cpct : IsCompact (f ⁻¹' {y}) := h_closed.isCompact
  exact h_cpct.finite h_disc

/-- **Partial discharge of `fibres_finite_statement`.** The full classical
statement reduces to a single uniform hypothesis: every fibre of a non-constant
analytic map carries the discrete subspace topology. This is what the chart-
level identity theorem would supply. The remainder of the argument
(closedness, compactness, finiteness from compact-discrete) is purely
topological and is discharged here. -/
lemma fibres_finite_of_all_fibers_isDiscrete
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_disc : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f → ∀ y : Y, IsDiscrete (f ⁻¹' {y})) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
      ∀ y : Y, (f ⁻¹' {y}).Finite := by
  intro f hf hnc y
  exact fiber_finite_of_isDiscrete hf.continuous y (h_disc f hf hnc y)

/-- A second, slightly more granular reduction: instead of a global
"all fibers are discrete" hypothesis, accept a per-fiber hypothesis. Useful
when downstream code knows discreteness only at specific values. -/
lemma fiber_finite_of_pointwise_isolated
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf_cont : Continuous f) (y : Y)
    (h_iso : ∀ x ∈ f ⁻¹' {y}, ∃ U : Set X, IsOpen U ∧ U ∩ f ⁻¹' {y} = {x}) :
    (f ⁻¹' {y}).Finite := by
  refine fiber_finite_of_isDiscrete hf_cont y ?_
  rw [isDiscrete_iff_forall_exists_isOpen]
  exact h_iso

end Owed.degree

end ContMDiff

end JacobianChallenge

end
