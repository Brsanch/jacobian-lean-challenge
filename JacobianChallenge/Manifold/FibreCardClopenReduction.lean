/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Degree

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Sharper reduction of `fibre_card_well_defined_statement` via a clopen level set

ZZ45 (`Manifold/Degree.lean`) reduced
`Owed.degree.fibre_card_well_defined_statement` to either

* the existence of a `FibreCardData f` (`fibre_card_well_defined_of_fibreCardData`),
  or
* the existence of a fibre-cardinality function `card_of` together with a
  preconnected regular-value subtype `R ⊆ Y` on which
  `card_of` restricted to `R` is `IsLocallyConstant`
  (`fibre_card_well_defined_of_locallyConstant`).

Both reductions ask for `IsLocallyConstant`, which is the *full*
covering-space content. The classical proof actually only needs constancy on
witness values, and the cleanest single-chip way to extract that is to ask
for **one level set** to be clopen — exactly the same shape as ZZ47's
discharge of `ClopennessOfLocallyConstHypothesis`: closed + open + nonempty
on a preconnected ambient gives everything.

This file provides a strictly sharper reduction:

> It suffices to produce, for every non-constant analytic `f`, a
> fibre-cardinality function `card_of`, a regular set `R ⊆ Y` carrying a
> preconnected subtype, and — for some witness value `y₀` of cardinality
> `n₀` — a single subset `L ⊆ R` such that
>
>   1. `L = {y ∈ R | card_of y = n₀}`,
>   2. `L` is clopen in the subtype `R`,
>   3. `L` is non-empty (e.g. via the witness),
>   4. every other witness's value also lies in `R`.
>
> Then `L = univ` (clopen + nonempty in preconnected ⇒ univ), so
> `card_of` agrees on every witness with `n₀`. Combined with
> `card_of_witness`-style readouts, this gives `w₁.card = w₂.card`.

The discharge is the standard
`IsClopen.eq_univ_of_isPreconnected`-flavoured argument applied via
`IsPreconnected.subset_isClopen` — a single chip, no path-walking, no
local identity theorem (those have already been used to prove the
input clopen-ness *if* the user wishes; here we accept clopen-ness as
the reduced obligation).

No `sorry`. No `axiom`. Signature of
`Owed.degree.fibre_card_well_defined_statement` unchanged. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-- **Helper.** Inside a preconnected subtype `R`, a clopen non-empty subset
is everything. This is the sub-`IsPreconnected.subset_isClopen` step packaged
for direct use on level sets of a `card_of` function. -/
lemma _root_.JacobianChallenge.ContMDiff.Owed.degree.preconnected_clopen_eq_univ
    {α : Type*} [TopologicalSpace α]
    {L : Set α}
    (hL_clopen : IsClopen L)
    (hL_nonempty : L.Nonempty)
    (h_pre : IsPreconnected (Set.univ : Set α)) :
    L = Set.univ := by
  -- A preconnected nonempty space has no proper clopen subset (other than
  -- itself). Equivalently: the only clopen subsets are `∅` and `univ`.
  -- Since `L` is clopen and nonempty, it equals `univ`.
  have h_pre_univ : IsPreconnected (Set.univ : Set α) := h_pre
  -- Decompose `univ = L ∪ Lᶜ` with both `L` and `Lᶜ` open and disjoint.
  have hL_open : IsOpen L := hL_clopen.2
  have hLc_open : IsOpen Lᶜ := hL_clopen.1.isOpen_compl
  have h_union : (Set.univ : Set α) ⊆ L ∪ Lᶜ := by
    intro x _; by_cases hx : x ∈ L
    · exact Or.inl hx
    · exact Or.inr hx
  have h_disjoint : Set.univ ∩ (L ∩ Lᶜ) = ∅ := by
    ext x
    simp [Set.mem_inter_iff, Set.mem_univ, Set.mem_compl_iff]
  -- Apply preconnectedness: one of `univ ∩ L`, `univ ∩ Lᶜ` is empty.
  have h_alt : (Set.univ ∩ L).Nonempty → (Set.univ ∩ Lᶜ).Nonempty →
      (Set.univ ∩ (L ∩ Lᶜ)).Nonempty :=
    h_pre_univ L Lᶜ hL_open hLc_open h_union
  -- `Set.univ ∩ L = L` is non-empty.
  have h_inL : (Set.univ ∩ L).Nonempty := by
    obtain ⟨x, hx⟩ := hL_nonempty
    exact ⟨x, ⟨Set.mem_univ x, hx⟩⟩
  -- If `Lᶜ` were non-empty, we'd get a contradiction with `h_disjoint`.
  by_contra h_ne
  have hLc_ne : (Lᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hL_eq
    exact h_ne hL_eq
  have h_ic_ne : (Set.univ ∩ Lᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hLc_ne
    exact ⟨x, ⟨Set.mem_univ x, hx⟩⟩
  have h_int_ne : (Set.univ ∩ (L ∩ Lᶜ)).Nonempty := h_alt h_inL h_ic_ne
  rw [h_disjoint] at h_int_ne
  exact h_int_ne.ne_empty rfl

/-- **Sharper reduction (clopen-level-set form).**

Suppose for every non-constant analytic `f` we are given a fibre-counting
function `card_of : Y → ℕ`, a regular set `R ⊆ Y` such that

* every `RegularValueWitness w` of `f` lies in `R` (`h_supp`),
* `card_of w.value = w.card` for every witness `w` (`h_witness`),
* the subtype `R` is preconnected (`h_conn_sub`),

and **for one specific witness's value `y₀` of cardinality `n₀ = card_of y₀`**
the level set
`L = {y : R | card_of y.val = n₀}`
is clopen in the subtype topology on `R` (`h_clopen`).

Then `L = univ`, so every witness has cardinality `n₀`, and any two
witnesses have equal `card`.

This is strictly weaker than the `IsLocallyConstant` hypothesis used in
`fibre_card_well_defined_of_locallyConstant`: one clopen level set rather
than every level set being open. -/
lemma fibre_card_eq_of_clopen_level_set
    {X : Type u} {Y : Type v} [TopologicalSpace Y]
    {f : X → Y}
    {R : Set Y}
    (card_of : Y → ℕ)
    (h_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card)
    (h_supp : ∀ w : RegularValueWitness f, w.value ∈ R)
    (h_conn_sub : IsPreconnected (Set.univ : Set R))
    (w₀ : RegularValueWitness f)
    (h_clopen :
      IsClopen ({y : R | card_of y.val = card_of w₀.value} : Set R))
    (w₁ w₂ : RegularValueWitness f) :
    w₁.card = w₂.card := by
  -- The level set `L = {y ∈ R | card_of y = card_of w₀.value}`.
  set L : Set R := {y : R | card_of y.val = card_of w₀.value} with hL_def
  -- It is non-empty: contains `⟨w₀.value, h_supp w₀⟩`.
  have h_w0_R : w₀.value ∈ R := h_supp w₀
  have h_w0_inL : (⟨w₀.value, h_w0_R⟩ : R) ∈ L := by
    show card_of w₀.value = card_of w₀.value
    rfl
  have hL_nonempty : L.Nonempty := ⟨_, h_w0_inL⟩
  -- Apply preconnected_clopen_eq_univ to conclude L = univ.
  have hL_univ : L = Set.univ :=
    preconnected_clopen_eq_univ h_clopen hL_nonempty h_conn_sub
  -- So both `w₁.value` and `w₂.value` (lifted to `R`) lie in `L`.
  have h_w1_R : w₁.value ∈ R := h_supp w₁
  have h_w2_R : w₂.value ∈ R := h_supp w₂
  have h_w1_inL : (⟨w₁.value, h_w1_R⟩ : R) ∈ L := by
    rw [hL_univ]; trivial
  have h_w2_inL : (⟨w₂.value, h_w2_R⟩ : R) ∈ L := by
    rw [hL_univ]; trivial
  -- `card_of w₁.value = card_of w₀.value` and similarly for `w₂`.
  have h_c1 : card_of w₁.value = card_of w₀.value := h_w1_inL
  have h_c2 : card_of w₂.value = card_of w₀.value := h_w2_inL
  have h_eq : card_of w₁.value = card_of w₂.value := h_c1.trans h_c2.symm
  -- Read off via h_witness.
  calc w₁.card
      = card_of w₁.value := (h_witness w₁).symm
    _ = card_of w₂.value := h_eq
    _ = w₂.card := h_witness w₂

/-- **Top-level sharper reduction.** `fibre_card_well_defined_statement`
follows from the existence, for every non-constant analytic `f`, of:

* a fibre-cardinality function `card_of : Y → ℕ`,
* a regular set `R ⊆ Y` containing every witness's value,
* preconnectedness of the subtype `R`,
* a chosen witness `w₀`,
* clopen-ness in the subtype `R` of the level set
  `{y : R | card_of y.val = card_of w₀.value}`.

This is the form a single ZZ47-style discharge would target: the
level-set's open-ness is the covering-space "fibre count is locally
constant" content, and its closed-ness is exactly the analytic
identity-theorem content from ZZ47. -/
lemma fibre_card_well_defined_of_clopen_level_set
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_data : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∃ (R : Set Y) (card_of : Y → ℕ) (w₀ : RegularValueWitness f),
        (∀ w : RegularValueWitness f, card_of w.value = w.card) ∧
        (∀ w : RegularValueWitness f, w.value ∈ R) ∧
        IsPreconnected (Set.univ : Set R) ∧
        IsClopen ({y : R | card_of y.val = card_of w₀.value} : Set R)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ JacobianChallenge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitness f), w₁.card = w₂.card := by
  intro f hf hnc w₁ w₂
  obtain ⟨R, card_of, w₀, h_w, h_supp, h_conn, h_clopen⟩ := h_data f hf hnc
  exact fibre_card_eq_of_clopen_level_set
    (R := R) card_of h_w h_supp h_conn w₀ h_clopen w₁ w₂

/-- **Equivalence with the locally-constant reduction.** A level set being
*clopen* in `R` is implied by the locally-constant + closed-level-set
combination, but is genuinely weaker: it asks for only *one* clopen level
set, not local-constancy of the whole function. The locally-constant route
already lives in `Manifold/Degree.lean`
(`fibre_card_well_defined_of_locallyConstant`); this clopen route is
strictly easier to discharge in the ZZ47 style.

Concretely: `IsLocallyConstant` ⇒ every level set is open *and* every level
set is closed (its complement being a union of opens). So in particular the
single chosen level set is clopen, witnessing this lemma is at most as hard
as the locally-constant lemma. -/
lemma clopen_level_set_of_isLocallyConstant
    {α : Type*} [TopologicalSpace α]
    {β : Type*} {g : α → β} (hg : IsLocallyConstant g) (b : β) :
    IsClopen ({a : α | g a = b} : Set α) := by
  refine ⟨?_, ?_⟩
  · -- closed: complement `{a | g a ≠ b}` is open by `IsLocallyConstant.isOpen_fiber`-style.
    have h_open : IsOpen ({a | g a = b}ᶜ : Set α) := by
      have := hg {b}ᶜ
      -- `g ⁻¹' {b}ᶜ = {a | g a ∈ {b}ᶜ} = {a | g a ≠ b} = {a | g a = b}ᶜ`
      simpa [Set.preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using this
    exact ⟨h_open⟩
  · -- open: `{a | g a = b} = g ⁻¹' {b}`, open by `IsLocallyConstant.isOpen_preimage` (`hg {b}`).
    have := hg {b}
    simpa [Set.preimage, Set.mem_singleton_iff] using this

end Owed.degree
end ContMDiff
end JacobianChallenge
