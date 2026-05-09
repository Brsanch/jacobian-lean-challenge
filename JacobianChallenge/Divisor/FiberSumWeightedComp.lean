/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single
import JacobianChallenge.Divisor.FiberSum
import JacobianChallenge.Divisor.FiberSumWeighted

set_option diagnostics.threshold 100

/-! # Contravariant composition for the weighted fibre sum (chip WFSC)

This file mirrors `Div.fiberSum_comp_apply` (`Divisor/FiberSum.lean`)
for the multiplicity-weighted fibre sum `Div.fiberSumWeighted`
(`Divisor/FiberSumWeighted.lean`).

Given `f : X → Y`, `g : Y → Z` with finite-fibre hypotheses and weight
functions `e_f : X → ℕ`, `e_g : Y → ℕ`, `e_gf : X → ℕ` satisfying the
multiplicativity condition `e_gf x = e_g (f x) * e_f x`, the identity

  `fiberSumWeighted (g ∘ f) hgf e_gf D
    = fiberSumWeighted f hf e_f (fiberSumWeighted g hg e_g D)`

holds for every `D : Div Z`. This is the divisor-side form of the
classical chain rule for ramification multiplicities; the analytic
content lives one floor up (in `manifoldRamificationIndex`).

The proof is purely algebraic: identical to the unweighted version
modulo bookkeeping for the per-point weights `(e _ : ℤ) • single _`.
-/

namespace JacobianChallenge

namespace Div

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [DecidableEq X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]

/-- The weighted fibre-sum on `Div.single y`: collapses the outer support
sum (which is `{y}`) and the trivial `1 • _` to leave just the fibre sum
with per-point weight `(e_f x : ℤ)`. -/
lemma fiberSumWeighted_single [DecidableEq Y]
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e_f : X → ℕ) (y : Y) :
    fiberSumWeighted f hf e_f (Div.single y)
      = ∑ x ∈ (hf y).toFinset, (e_f x : ℤ) • Div.single x := by
  classical
  show fiberSumWeightedFun f hf e_f (Div.single y)
        = ∑ x ∈ (hf y).toFinset, (e_f x : ℤ) • Div.single x
  have hsub : (Div.single y : Div Y).supportFinset ⊆ ({y} : Finset Y) := by
    intro z hz
    rw [supportFinset_single] at hz
    exact hz
  rw [fiberSumWeightedFun_eq_sum f hf e_f (Div.single y) ({y} : Finset Y) hsub,
      Finset.sum_singleton, single_apply, if_pos rfl, one_smul]

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [DecidableEq Y]

/-- Contravariant composition for the *weighted* fibre sum.

If the per-point weights satisfy the multiplicativity condition
`e_gf x = e_g (f x) * e_f x`, then

  `fiberSumWeighted (g ∘ f) hgf e_gf
    = fiberSumWeighted f hf e_f ∘ fiberSumWeighted g hg e_g`

on every divisor. The unweighted `Div.fiberSum_comp_apply` is recovered
by setting `e_f ≡ e_g ≡ e_gf ≡ 1`. -/
lemma fiberSumWeighted_comp_apply
    (f : X → Y) (g : Y → Z)
    (hf : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (hg : ∀ z : Z, (g ⁻¹' {z}).Finite)
    (hgf : ∀ z : Z, ((g ∘ f) ⁻¹' {z}).Finite)
    (e_f : X → ℕ) (e_g : Y → ℕ) (e_gf : X → ℕ)
    (h_e_prod : ∀ x, e_gf x = e_g (f x) * e_f x)
    (D : Div Z) :
    fiberSumWeighted (g ∘ f) hgf e_gf D
      = fiberSumWeighted f hf e_f (fiberSumWeighted g hg e_g D) := by
  classical
  -- Step 1: rewrite the inner `fiberSumWeighted g hg e_g D` as its
  -- finset-sum form.
  have hg_eq : fiberSumWeighted g hg e_g D
      = ∑ z ∈ D.supportFinset,
          D z • (∑ y ∈ (hg z).toFinset, (e_g y : ℤ) • Div.single y) := by
    show fiberSumWeightedFun g hg e_g D = _
    rfl
  -- Step 2: rewrite the LHS `fiberSumWeighted (g ∘ f) hgf e_gf D` similarly.
  have hLHS : fiberSumWeighted (g ∘ f) hgf e_gf D
      = ∑ z ∈ D.supportFinset, D z •
          ∑ x ∈ (hgf z).toFinset, (e_gf x : ℤ) • (Div.single x : Div X) := by
    show fiberSumWeightedFun (g ∘ f) hgf e_gf D = _
    rfl
  rw [hLHS, hg_eq, map_sum (fiberSumWeighted f hf e_f)]
  refine Finset.sum_congr rfl ?_
  intro z _
  -- Push through the outer ℤ-smul `D z • _` and the inner sum.
  rw [map_zsmul, map_sum (fiberSumWeighted f hf e_f)]
  -- Strip the common `D z • ·`, reducing to a pure sum equality.
  congr 1
  -- Goal:
  --   ∑ x ∈ (hgf z).toFinset, (e_gf x : ℤ) • single x
  --     = ∑ y ∈ (hg z).toFinset,
  --         fiberSumWeighted f hf e_f ((e_g y : ℤ) • single y)
  -- Disjointness of the fibre family (identical to unweighted version).
  have hdisj : ((hg z).toFinset : Set Y).PairwiseDisjoint
      (fun y => (hf y).toFinset) := by
    intro y₁ _ y₂ _ hne
    show Disjoint ((hf y₁).toFinset) ((hf y₂).toFinset)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [Set.Finite.mem_toFinset] at hx₁ hx₂
    have e1 : f x = y₁ := hx₁
    have e2 : f x = y₂ := hx₂
    exact hne (e1.symm.trans e2)
  -- The finset equality `(hgf z).toFinset = (hg z).toFinset.biUnion (...)`.
  have hset_eq : (hgf z).toFinset
      = (hg z).toFinset.biUnion (fun y => (hf y).toFinset) := by
    ext x
    rw [Finset.mem_biUnion, Set.Finite.mem_toFinset]
    constructor
    · intro hx
      have hgfx : g (f x) = z := hx
      refine ⟨f x, ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]; exact hgfx
      · rw [Set.Finite.mem_toFinset]; rfl
    · rintro ⟨y, hy, hxy⟩
      rw [Set.Finite.mem_toFinset] at hy hxy
      have e : f x = y := hxy
      show g (f x) = z
      rw [e]; exact hy
  -- Decompose the LHS using `Finset.sum_biUnion`.
  rw [hset_eq, Finset.sum_biUnion hdisj]
  -- New goal:
  --   ∑ y ∈ (hg z).toFinset, ∑ x ∈ (hf y).toFinset, (e_gf x : ℤ) • single x
  --     = ∑ y ∈ (hg z).toFinset,
  --         fiberSumWeighted f hf e_f ((e_g y : ℤ) • single y)
  refine Finset.sum_congr rfl ?_
  intro y hy
  rw [Set.Finite.mem_toFinset] at hy
  -- `hy : y ∈ g ⁻¹' {z}`, only used implicitly. The real content is on
  -- the inner fibre `(hf y).toFinset`: every `x` there has `f x = y`.
  -- Step A: simplify the RHS via `map_zsmul` and `fiberSumWeighted_single`.
  rw [map_zsmul, fiberSumWeighted_single f hf e_f y]
  -- New goal:
  --   ∑ x ∈ (hf y).toFinset, (e_gf x : ℤ) • single x
  --     = (e_g y : ℤ) • ∑ x ∈ (hf y).toFinset, (e_f x : ℤ) • single x
  -- Push `(e_g y : ℤ) • _` through the sum and rewrite each summand.
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  have hfx : f x = y := hx
  -- `(e_g y : ℤ) • (e_f x : ℤ) • single x = ((e_g y * e_f x : ℕ) : ℤ) • single x`.
  rw [smul_smul]
  -- Goal: `(e_gf x : ℤ) • single x = ((e_g y : ℤ) * (e_f x : ℤ)) • single x`.
  -- Use `h_e_prod x` and `f x = y`.
  have hcoef : (e_gf x : ℤ) = (e_g y : ℤ) * (e_f x : ℤ) := by
    have := h_e_prod x
    rw [hfx] at this
    exact_mod_cast this
  rw [hcoef]

end Div

end JacobianChallenge
