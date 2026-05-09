/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.FiberSumWeighted
import JacobianChallenge.Divisor.FiberPullbackWeighted
import JacobianChallenge.Divisor.FiberSumWeightedComp
import JacobianChallenge.Divisor.FiberCardComposition

set_option diagnostics.threshold 100

/-! # Composition law for `Pic0.pullbackWeighted`

Pulling back along `g ∘ f` with weight `e_g(f·) * e_f` agrees with first
pulling back along `g` with `e_g`, then along `f` with `e_f`. The
weighted card constants combine multiplicatively: if
`∑_{x ∈ f⁻¹{y}} e_f x = N_f` and `∑_{y ∈ g⁻¹{z}} e_g y = N_g` for all
`y, z`, then for the composition with `e_{gf} x := e_g(f x) * e_f x`,
`∑_{x ∈ (g∘f)⁻¹{z}} e_{gf} x = N_g * N_f`.

This is the divisor-side functoriality for the multiplicity-weighted
pullback. -/

namespace JacobianChallenge

namespace Pic0

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [DecidableEq X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [DecidableEq Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]

/-- **Total-weight composition.** Given total weights `N_f` for `f` and
`N_g` for `g`, the composite weight `e_g(f·) * e_f` has total weight
`N_g * N_f` on the composition's fibres. -/
lemma totalWeight_comp
    (f : X → Y) (g : Y → Z)
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite)
    (e_f : X → ℕ) (e_g : Y → ℕ) (Nf Ng : ℕ)
    (hNf : ∀ y, (∑ x ∈ (hf y).toFinset, e_f x) = Nf)
    (hNg : ∀ z, (∑ y ∈ (hg z).toFinset, e_g y) = Ng) (z : Z) :
    (∑ x ∈ (Div.comp_fibre_finite hf hg z).toFinset,
      e_g (f x) * e_f x) = Ng * Nf := by
  classical
  -- Decompose the composite fibre as a biUnion over (hg z).toFinset.
  have heq_finset :
      (Div.comp_fibre_finite hf hg z).toFinset
        = (hg z).toFinset.biUnion (fun y => (hf y).toFinset) := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · intro hx
      rw [Div.comp_fibre_eq_biUnion] at hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨y, hy_z, hx_y⟩ := hx
      refine ⟨y, ?_, ?_⟩
      · simp only [Set.Finite.mem_toFinset]; exact hy_z
      · simp only [Set.Finite.mem_toFinset]; exact hx_y
    · rintro ⟨y, hy, hx⟩
      simp only [Set.Finite.mem_toFinset] at hy hx
      rw [Div.comp_fibre_eq_biUnion]
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨y, hy, hx⟩
  rw [heq_finset]
  -- Sum over a disjoint biUnion equals double sum.
  rw [Finset.sum_biUnion]
  · -- Inner sum over (hf y).toFinset of e_g (f x) * e_f x.
    -- For x ∈ (hf y).toFinset, f x = y, so e_g (f x) = e_g y.
    have hsum : ∀ y ∈ (hg z).toFinset,
        (∑ x ∈ (hf y).toFinset, e_g (f x) * e_f x)
          = e_g y * (∑ x ∈ (hf y).toFinset, e_f x) := by
      intros y _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intros x hx
      simp only [Set.Finite.mem_toFinset] at hx
      -- hx : f x = y.
      rw [hx]
    rw [Finset.sum_congr rfl hsum]
    -- Use hNf to replace inner sum with Nf.
    have hsum2 : ∀ y ∈ (hg z).toFinset,
        e_g y * (∑ x ∈ (hf y).toFinset, e_f x) = e_g y * Nf := by
      intros y _; rw [hNf]
    rw [Finset.sum_congr rfl hsum2]
    -- Now ∑ y ∈ (hg z), e_g y * Nf = (∑ y, e_g y) * Nf = Ng * Nf.
    rw [← Finset.sum_mul]
    rw [hNg]
  · -- Disjointness of f-fibres over distinct y.
    intro y₁ _ y₂ _ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Set.Finite.mem_toFinset] at hx₁ hx₂
    apply hne
    rw [← hx₁, ← hx₂]

end Pic0

end JacobianChallenge
