/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.FiberPullback

set_option diagnostics.threshold 100

/-! # Fibre cardinality and finiteness through composition -/

namespace JacobianChallenge

namespace Div

variable {X Y Z : Type*}

/-- **Fibre of a composition decomposes by intermediate fibre.** -/
lemma comp_fibre_eq_biUnion (f : X → Y) (g : Y → Z) (z : Z) :
    (g ∘ f) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp,
             Set.mem_iUnion, exists_prop]
  exact ⟨fun h => ⟨f x, h, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩

/-- **Composition of finite fibres is finite.** -/
lemma comp_fibre_finite
    {f : X → Y} {g : Y → Z}
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite) (z : Z) :
    ((g ∘ f) ⁻¹' {z}).Finite := by
  rw [comp_fibre_eq_biUnion]
  exact Set.Finite.biUnion (hg z) (fun y _ => hf y)

/-- **Composition of constant-card fibres has constant card `Ng * Nf`.** -/
lemma comp_fibre_card
    {f : X → Y} {g : Y → Z} [DecidableEq Y]
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite)
    (Nf Ng : ℕ)
    (hNf : ∀ y, (hf y).toFinset.card = Nf)
    (hNg : ∀ z, (hg z).toFinset.card = Ng)
    (z : Z) :
    ((comp_fibre_finite hf hg z).toFinset).card = Ng * Nf := by
  classical
  -- Show the toFinset equals the biUnion finset, then count.
  have heq_finset :
      (comp_fibre_finite hf hg z).toFinset
        = (hg z).toFinset.biUnion (fun y => (hf y).toFinset) := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · intro hx
      rw [comp_fibre_eq_biUnion] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨y, hy_z, hx_y⟩ := hx
      refine ⟨y, ?_, ?_⟩
      · simp only [Set.Finite.mem_toFinset]; exact hy_z
      · simp only [Set.Finite.mem_toFinset]; exact hx_y
    · rintro ⟨y, hy, hx⟩
      simp only [Set.Finite.mem_toFinset] at hy hx
      rw [comp_fibre_eq_biUnion]
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨y, hy, hx⟩
  rw [heq_finset]
  -- Apply Finset.card_biUnion with disjointness.
  rw [Finset.card_biUnion]
  · -- Each summand is Nf, summed over Ng terms.
    have heach : ∀ y ∈ (hg z).toFinset, (hf y).toFinset.card = Nf := by
      intros y _
      exact hNf y
    rw [Finset.sum_congr rfl heach]
    rw [Finset.sum_const, smul_eq_mul, hNg z]
  · -- Disjointness: f-fibres over distinct y are disjoint.
    intro y₁ _ y₂ _ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Set.Finite.mem_toFinset] at hx₁ hx₂
    -- hx₁ : f x = y₁, hx₂ : f x = y₂.
    apply hne
    rw [← hx₁, ← hx₂]

end Div

end JacobianChallenge
