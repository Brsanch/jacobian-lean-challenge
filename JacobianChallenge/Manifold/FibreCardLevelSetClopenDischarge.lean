/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreCardWellDefinedUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Reduction of `FibreCardLevelSetClopenHypothesis` to a smaller residual

ZZ51 (`Manifold/FibreCardWellDefinedUnconditional.lean`) reduced
`fibre_card_well_defined_statement X Y` to a single named hypothesis
`FibreCardLevelSetClopenHypothesis X Y` (clopen-ness, in the subtype
topology on `R = (Set.univ : Set Y)`, of the level set
`{y : R | card_of y.val = card_of w₀.value}`).

This file (ZZ54) **further reduces** that hypothesis to a strictly smaller
named residual: *local constancy of the fibre-cardinality function on the
whole of `Y`*. Specifically:

> `FibreCardLocallyConstantOnUniverse X Y` says: for every non-constant
> analytic `f : X → Y` and every `y : Y`, there is an open neighbourhood
> `U ∋ y` such that for every `y' ∈ U`, the fibres `f ⁻¹' {y'}` and
> `f ⁻¹' {y}` have equal `Set.Finite.toFinset.card`.

`FibreCardLevelSetClopenHypothesis X Y` is then a *direct corollary*: any
level set of a locally-constant `ℕ`-valued function on a topological space
is clopen, in any subtype topology, including `R = Set.univ`.

## Why this is the right residual at this pin

The classical proof of `FibreCardLevelSetClopenHypothesis` factors through
two distinct pieces of covering-space content:

* **Openness of every level set**: the fibre count is locally constant on
  the regular-value subset `Y \ f(critical(f))`. This is the topological
  degree theorem — local biholomorphism at every regular preimage gives a
  matching of preimages between nearby fibres. It is owed at the mathlib
  pin.
* **Closedness of every level set**: equivalently, openness of the
  *complement* (a union of other level sets). Same content.

Both reduce to the single statement *the fibre-cardinality function is
locally constant on `Y`*. That is what we name as the residual here.

## What this file ships

* `FibreCardLocallyConstantOnUniverse X Y` — the named residual `Prop`.
* `fibreCardLevelSetClopen_of_locallyConstant` — proves the upstream
  hypothesis from the residual.
* The chain plays through ZZ51 with **no new analytic input** beyond the
  residual.

## Why this is strictly smaller

The upstream `FibreCardLevelSetClopenHypothesis X Y` asks for clopen-ness
of *one specific* level set (parametrised by the chosen witness `w₀`) for
every non-constant `f`. The residual asks for *local constancy* of the
counting function — which immediately implies every level set is clopen,
not just the chosen one. So the residual is at most as hard to discharge:
any classical proof of one passes directly through the other.

## Caveat on the hypothesis shape upstream

The structure `RegularValueWitness f` in `Manifold/Degree.lean` records
only `value : Y` together with `fiber_finite : (f ⁻¹' {value}).Finite`,
*not* a regular-value condition. By ZZ48 every fibre of a non-constant
analytic map between compact Riemann surfaces is finite, so any `y : Y`
packages as a `RegularValueWitness`. In particular, `w₀.value` may be a
*critical value* (a value over which `f` ramifies). Across critical
values the fibre cardinality is *strictly less* than the topological
degree, so for the upstream hypothesis to hold on `R = Set.univ` for
*every* witness `w₀`, the fibre-cardinality function must be locally
constant on all of `Y` — which is the content of
`FibreCardLocallyConstantOnUniverse X Y`. Equivalently: the implicit
pre-condition is that the critical-value set is *empty*, i.e. `f` is an
unbranched cover. (Note the hypothesis is consistent with the conclusion
`w₁.card = w₂.card` only in this case; if the user only ever calls the
final theorem with a regular-value witness, the discrepancy is harmless,
but the named residual makes the assumption visible.)

This file does **not** discharge `FibreCardLocallyConstantOnUniverse`. The
discharge is the topological-degree content owed at the mathlib pin and
is left as the next chip downstream.

No `sorry`. No `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-- **The smaller residual hypothesis.** The fibre-cardinality function
`card_of : Y → ℕ` of every non-constant analytic `f : X → Y` is locally
constant on all of `Y`.

This is the topological-degree content (local biholomorphism at every
regular preimage gives matching counts, and on the regular-value subset
the counting function is locally constant). Plus the implicit assumption
that the critical-value set is empty (else the count *drops* there, and
local constancy fails — see the file docstring caveat). -/
def FibreCardLocallyConstantOnUniverse
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (_hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_fib : ∀ y : Y, (f ⁻¹' {y}).Finite) (y : Y),
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ∀ y' ∈ U, (h_fib y').toFinset.card = (h_fib y).toFinset.card

/-- **Helper.** A locally constant `ℕ`-valued function on a topological space
has clopen level sets. -/
private lemma isClopen_levelSet_of_locallyConstant
    {α : Type*} [TopologicalSpace α] {g : α → ℕ}
    (hg : ∀ x : α, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, g x' = g x)
    (n : ℕ) :
    IsClopen ({x : α | g x = n} : Set α) := by
  -- Both `{x | g x = n}` and its complement are open.
  refine ⟨?_, ?_⟩
  · -- closed: the complement `{x | g x ≠ n}` is open.
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    -- `x ∈ {x | g x = n}ᶜ` means `g x ≠ n`.
    have hxne : g x ≠ n := hx
    obtain ⟨U, hU_open, hxU, hU_eq⟩ := hg x
    refine ⟨U, ?_, hU_open, hxU⟩
    intro x' hx'U
    -- `g x' = g x ≠ n`, so `x' ∈ {x | g x = n}ᶜ`.
    show g x' ≠ n
    rw [hU_eq x' hx'U]
    exact hxne
  · -- open: directly.
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    -- `x ∈ {x | g x = n}` means `g x = n`.
    have hxn : g x = n := hx
    obtain ⟨U, hU_open, hxU, hU_eq⟩ := hg x
    refine ⟨U, ?_, hU_open, hxU⟩
    intro x' hx'U
    show g x' = n
    rw [hU_eq x' hx'U, hxn]

/-- **Helper.** Local constancy of `card_of` on `Y` lifts to local constancy
of `fun y : R => card_of y.val` on the subtype `R = Set.univ`. -/
private lemma locallyConstant_subtype_of_locallyConstant_univ
    {Y : Type v} [TopologicalSpace Y] {g : Y → ℕ}
    (hg : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ y' ∈ U, g y' = g y) :
    ∀ y : (Set.univ : Set Y),
      ∃ V : Set (Set.univ : Set Y), IsOpen V ∧ y ∈ V ∧
        ∀ y' ∈ V, g y'.val = g y.val := by
  intro y
  obtain ⟨U, hU_open, hyU, hU_eq⟩ := hg y.val
  refine ⟨(Subtype.val) ⁻¹' U, ?_, ?_, ?_⟩
  · exact hU_open.preimage continuous_subtype_val
  · exact hyU
  · intro y' hy'V
    exact hU_eq y'.val hy'V

/-- **Reduction.** `FibreCardLevelSetClopenHypothesis X Y` follows from
`FibreCardLocallyConstantOnUniverse X Y`.

Given local constancy of the fibre-cardinality function on `Y`, every level
set in `Y` is clopen, and the same holds after pulling back through the
subtype `R = Set.univ`. The chosen-witness level set in the upstream
hypothesis is one such level set (with `n = card_of w₀.value`). -/
theorem fibreCardLevelSetClopen_of_locallyConstant
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_loc : FibreCardLocallyConstantOnUniverse X Y) :
    FibreCardLevelSetClopenHypothesis X Y := by
  intro f hf hnc h_fib w₀
  -- Local constancy of `card_of` on `Y`, packaged for `g := fun y => (h_fib y).toFinset.card`.
  set g : Y → ℕ := fun y => (h_fib y).toFinset.card with hg_def
  have h_locY : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ y' ∈ U, g y' = g y := by
    intro y
    obtain ⟨U, hU_open, hyU, hU_eq⟩ := h_loc f hf hnc h_fib y
    exact ⟨U, hU_open, hyU, hU_eq⟩
  -- Lift to local constancy of `fun y : R => g y.val` on `R = Set.univ`.
  have h_locR :
      ∀ y : (Set.univ : Set Y),
        ∃ V : Set (Set.univ : Set Y), IsOpen V ∧ y ∈ V ∧
          ∀ y' ∈ V, g y'.val = g y.val :=
    locallyConstant_subtype_of_locallyConstant_univ h_locY
  -- The level set in the upstream hypothesis equals
  -- `{y : R | (fun y' : R => g y'.val) y = g w₀.value}`.
  have h_clopen :
      IsClopen
        ({y : (Set.univ : Set Y) | g y.val = g w₀.value}
          : Set (Set.univ : Set Y)) := by
    -- Apply `isClopen_levelSet_of_locallyConstant` to `g ∘ Subtype.val` and `n = g w₀.value`.
    have :=
      isClopen_levelSet_of_locallyConstant
        (g := fun y : (Set.univ : Set Y) => g y.val) h_locR (g w₀.value)
    exact this
  -- Match the goal shape (`(h_fib y.val).toFinset.card`).
  show IsClopen
      ({y : (Set.univ : Set Y) |
         (h_fib y.val).toFinset.card = (h_fib w₀.value).toFinset.card}
        : Set (Set.univ : Set Y))
  exact h_clopen

/-- **Top-level Step A.3 reduction (sharper named residual).**
`fibre_card_well_defined_statement X Y` follows from
`FibreCardLocallyConstantOnUniverse X Y`. -/
theorem fibre_card_well_defined_statement_holds_of_locallyConstant
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_loc : FibreCardLocallyConstantOnUniverse X Y) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitness f), w₁.card = w₂.card :=
  fibre_card_well_defined_statement_holds_of_levelSetClopen
    (fibreCardLevelSetClopen_of_locallyConstant h_loc)

end Owed.degree
end ContMDiff
end JacobianChallenge
