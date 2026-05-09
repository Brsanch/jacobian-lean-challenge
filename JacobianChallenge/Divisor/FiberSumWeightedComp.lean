/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.FiberSumWeighted
import JacobianChallenge.Divisor.FiberCardComposition
import JacobianChallenge.Divisor.Single

set_option diagnostics.threshold 100

/-! # Composition law for the weighted fibre sum (pointwise version)

For composable maps `f : X → Y` and `g : Y → Z` with finite fibres, and
weights `e_f : X → ℕ`, `e_g : Y → ℕ`:

```
fiberSumWeighted f hf e_f (fiberSumWeighted g hg e_g (Div.single z))
  = fiberSumWeighted (g ∘ f) hgf w (Div.single z)
```

where `w x := e_g (f x) * e_f x`. This is the divisor-side composition
law for the multiplicity-weighted pullback. The proof works pointwise:
both sides evaluate at any `x₀` to `e_g (f x₀) * e_f x₀` if
`(g ∘ f)(x₀) = z` and `0` otherwise. -/

namespace JacobianChallenge

namespace Div

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [DecidableEq X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [DecidableEq Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]

/-- Pointwise value of the weighted fibre sum applied to `Div.single z`. -/
private lemma fiberSumWeighted_single_apply
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ)
    (z : Y) (x₀ : X) :
    ((Div.fiberSumWeighted f hf e (Div.single z) : Div X) : X → ℤ) x₀
      = if x₀ ∈ (hf z).toFinset then (e x₀ : ℤ) else 0 := by
  classical
  show ((Div.fiberSumWeightedFun f hf e (Div.single z) : Div X) : X → ℤ) x₀
      = _
  unfold Div.fiberSumWeightedFun
  -- support of single z is {z}; (single z) z = 1, else 0.
  have hsub : (Div.single z : Div Y).supportFinset ⊆ ({z} : Finset Y) := by
    intro y hy
    rw [Div.supportFinset_single] at hy; exact hy
  rw [Div.fiberSumWeightedFun_eq_sum f hf e (Div.single z) ({z} : Finset Y) hsub
    |>.symm.trans (by rw [Div.fiberSumWeightedFun_eq_sum f hf e
        (Div.single z) ({z} : Finset Y) hsub])]
  rw [Finset.sum_singleton]
  -- (Div.single z) z = 1.
  rw [Div.single_apply, if_pos rfl]
  -- 1 • (∑ x ∈ (hf z).toFinset, (e x : ℤ) • Div.single x)
  rw [one_smul]
  -- Pointwise application of the inner sum.
  rw [Function.locallyFinsuppWithin.coe_sum]
  simp only [Finset.sum_apply]
  -- Each summand: ((e x : ℤ) • Div.single x) x₀ = e x * (if x₀ = x then 1 else 0).
  have hpt : ∀ x ∈ (hf z).toFinset,
      (((e x : ℤ) • (Div.single x : Div X) : Div X) : X → ℤ) x₀
        = (e x : ℤ) * (if x₀ = x then 1 else 0) := by
    intros x _
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
        Div.single_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl hpt]
  -- Sum over x ∈ (hf z).toFinset of e x * (if x₀ = x then 1 else 0).
  -- This is e x₀ if x₀ ∈ (hf z).toFinset, else 0.
  by_cases hx₀ : x₀ ∈ (hf z).toFinset
  · rw [if_pos hx₀]
    rw [Finset.sum_eq_single x₀]
    · simp
    · intro x _ hxne
      rw [if_neg (fun h => hxne h.symm), mul_zero]
    · intro hx₀'
      exact absurd hx₀ hx₀'
  · rw [if_neg hx₀]
    rw [Finset.sum_eq_zero]
    intros x hx
    by_cases hxx₀ : x₀ = x
    · subst hxx₀; exact absurd hx hx₀
    · rw [if_neg hxx₀, mul_zero]

/-- Pointwise value of the unweighted-style biUnion fibre sum applied to
`Div.single z`. -/
private lemma fiberSumWeighted_comp_single_apply
    (f : X → Y) (g : Y → Z)
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite)
    (hgf : ∀ z, ((g ∘ f) ⁻¹' {z}).Finite)
    (e_f : X → ℕ) (e_g : Y → ℕ) (z : Z) (x₀ : X) :
    ((Div.fiberSumWeighted f hf e_f
        (Div.fiberSumWeighted g hg e_g (Div.single z)) : Div X) : X → ℤ) x₀
      = ((Div.fiberSumWeighted (g ∘ f) hgf
          (fun x => e_g (f x) * e_f x) (Div.single z) : Div X) : X → ℤ) x₀ := by
  classical
  -- RHS is straightforward: by the pointwise lemma, equals
  --   (e_g (f x₀) * e_f x₀ : ℤ) if x₀ ∈ (hgf z).toFinset, else 0.
  rw [fiberSumWeighted_single_apply]
  -- LHS: expand outer fiberSumWeighted f at x₀ pointwise.
  -- The inner argument D := fiberSumWeighted g hg e_g (single z) has the
  -- structure: D y = e_g y if y ∈ (hg z).toFinset, else 0.
  -- Outer: fiberSumWeighted f hf e_f D = ∑ y ∈ supp D, D y • (∑ x ∈ (hf y).toFinset, (e_f x : ℤ) • single x).
  -- We first replace the support sum by a sum over (hg z).toFinset (terms with D y = 0 vanish).
  set D : Div Y := Div.fiberSumWeighted g hg e_g (Div.single z) with hD_def
  -- We compute (Div.fiberSumWeighted f hf e_f D : Div X) x₀ via the
  -- standard expansion using the support `(hg z).toFinset`.
  have hsuppD : D.supportFinset ⊆ (hg z).toFinset := by
    intro y hy
    rw [Div.mem_supportFinset] at hy
    -- D y ≠ 0, so by the pointwise formula, y ∈ (hg z).toFinset.
    rw [hD_def] at hy
    rw [fiberSumWeighted_single_apply g hg e_g z y] at hy
    by_contra hy_not
    apply hy
    show (D : Y → ℤ) y = 0
    rw [hD_def]
    show ((Div.fiberSumWeighted g hg e_g (Div.single z) : Div Y) : Y → ℤ) y = 0
    rw [fiberSumWeighted_single_apply g hg e_g z y]
    rw [if_neg hy_not]
  -- Now use fiberSumWeightedFun_eq_sum to extend to (hg z).toFinset.
  show ((Div.fiberSumWeightedFun f hf e_f D : Div X) : X → ℤ) x₀ = _
  rw [Div.fiberSumWeightedFun_eq_sum f hf e_f D _ hsuppD]
  -- Goal: pointwise eval of (∑ y ∈ (hg z).toFinset, D y • (∑ x ∈ (hf y).toFinset, e_f x • single x)) at x₀.
  rw [Function.locallyFinsuppWithin.coe_sum]
  simp only [Finset.sum_apply]
  -- Compute D y for y ∈ (hg z).toFinset: by pointwise formula, = e_g y.
  have hD_val : ∀ y ∈ (hg z).toFinset, (D : Y → ℤ) y = (e_g y : ℤ) := by
    intros y hy
    rw [hD_def]
    show ((Div.fiberSumWeighted g hg e_g (Div.single z) : Div Y) : Y → ℤ) y = _
    rw [fiberSumWeighted_single_apply g hg e_g z y]
    rw [if_pos hy]
  -- Now: ∑ y ∈ (hg z).toFinset, ((D y) • (inner sum)) at x₀
  --   = ∑ y ∈ (hg z).toFinset, D y * (inner sum at x₀)
  --   = ∑ y, e_g y * (e_f x₀ if x₀ ∈ (hf y).toFinset else 0)
  have hpt : ∀ y ∈ (hg z).toFinset,
      (((D : Div Y) y • (∑ x ∈ (hf y).toFinset, (e_f x : ℤ) • Div.single x) : Div X)
        : X → ℤ) x₀
        = (e_g y : ℤ) *
          (if x₀ ∈ (hf y).toFinset then (e_f x₀ : ℤ) else 0) := by
    intros y hy
    rw [hD_val y hy]
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
    congr 1
    -- (∑ x ∈ (hf y).toFinset, e_f x • single x) at x₀
    --   = e_f x₀ if x₀ ∈ (hf y).toFinset, else 0.
    rw [Function.locallyFinsuppWithin.coe_sum]
    simp only [Finset.sum_apply]
    have hpt2 : ∀ x ∈ (hf y).toFinset,
        (((e_f x : ℤ) • (Div.single x : Div X) : Div X) : X → ℤ) x₀
          = (e_f x : ℤ) * (if x₀ = x then 1 else 0) := by
      intros x _
      rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
          Div.single_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl hpt2]
    by_cases hx₀ : x₀ ∈ (hf y).toFinset
    · rw [if_pos hx₀]
      rw [Finset.sum_eq_single x₀]
      · simp
      · intros x _ hxne
        rw [if_neg (fun h => hxne h.symm), mul_zero]
      · intros hx₀'
        exact absurd hx₀ hx₀'
    · rw [if_neg hx₀]
      rw [Finset.sum_eq_zero]
      intros x hx
      by_cases hxx₀ : x₀ = x
      · subst hxx₀; exact absurd hx hx₀
      · rw [if_neg hxx₀, mul_zero]
  rw [Finset.sum_congr rfl hpt]
  -- LHS now: ∑ y ∈ (hg z).toFinset, e_g y * (e_f x₀ if x₀ ∈ (hf y).toFinset else 0).
  -- The "if" filters to y such that x₀ ∈ (hf y).toFinset, i.e., f x₀ = y.
  -- For x₀: at most one such y, namely y = f x₀, and only if f x₀ ∈ (hg z).toFinset
  -- (which means g (f x₀) = z).
  -- So sum is e_g (f x₀) * e_f x₀ if both x₀ ∈ fibre and f x₀ ∈ (hg z).toFinset,
  -- else 0.
  -- The both-conditions reduces to (g ∘ f) x₀ = z, i.e., x₀ ∈ (hgf z).toFinset.
  by_cases hgf_x₀ : x₀ ∈ (hgf z).toFinset
  · -- (g ∘ f) x₀ = z. Then f x₀ ∈ (hg z).toFinset (since g (f x₀) = z), and
    -- x₀ ∈ (hf (f x₀)).toFinset (trivially, f x₀ = f x₀).
    rw [if_pos hgf_x₀]
    have hfx₀_g : f x₀ ∈ (hg z).toFinset := by
      rw [Set.Finite.mem_toFinset]
      show g (f x₀) = z
      rw [Set.Finite.mem_toFinset] at hgf_x₀
      exact hgf_x₀
    have hx₀_hf : x₀ ∈ (hf (f x₀)).toFinset := by
      rw [Set.Finite.mem_toFinset]
      show f x₀ = f x₀
      rfl
    rw [Finset.sum_eq_single (f x₀)]
    · rw [if_pos hx₀_hf]
      ring
    · intros y hy_g hyne
      -- For y ≠ f x₀ in (hg z).toFinset, the inner if is "x₀ ∈ (hf y).toFinset",
      -- i.e., f x₀ = y. But y ≠ f x₀, so f x₀ ≠ y, so "if" is false.
      rw [if_neg]
      · ring
      · rw [Set.Finite.mem_toFinset]
        intro hf_eq
        -- hf_eq : f x₀ = y, but hyne : y ≠ f x₀.
        exact hyne hf_eq.symm
    · intros hfx₀_g'
      exact absurd hfx₀_g hfx₀_g'
  · -- (g ∘ f) x₀ ≠ z. Then either f x₀ ∉ (hg z).toFinset, or x₀ ∉ (hf y).toFinset
    -- for any y in support. In either case, all sum terms vanish.
    rw [if_neg hgf_x₀]
    rw [Finset.sum_eq_zero]
    intros y hy
    by_cases hx₀_y : x₀ ∈ (hf y).toFinset
    · -- x₀ ∈ fibre of y under f, i.e., f x₀ = y.
      -- y ∈ (hg z).toFinset means g y = z. So g (f x₀) = z, contradicting hgf_x₀.
      rw [Set.Finite.mem_toFinset] at hx₀_y hy
      exfalso
      apply hgf_x₀
      rw [Set.Finite.mem_toFinset]
      show g (f x₀) = z
      have : f x₀ = y := hx₀_y
      rw [this]
      exact hy
    · rw [if_neg hx₀_y, mul_zero]

/-- **Composition law for the weighted fibre sum on `Div.single z`.**
The composition of weighted fibre sums equals a weighted fibre sum of
the composition with weight `e_g(f x) * e_f(x)`. -/
lemma fiberSumWeighted_comp_single
    (f : X → Y) (g : Y → Z)
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite)
    (hgf : ∀ z, ((g ∘ f) ⁻¹' {z}).Finite)
    (e_f : X → ℕ) (e_g : Y → ℕ) (z : Z) :
    Div.fiberSumWeighted f hf e_f
        (Div.fiberSumWeighted g hg e_g (Div.single z))
      = Div.fiberSumWeighted (g ∘ f) hgf
          (fun x => e_g (f x) * e_f x) (Div.single z) := by
  refine DFunLike.ext _ _ ?_
  intro x₀
  exact fiberSumWeighted_comp_single_apply f g hf hg hgf e_f e_g z x₀

end Div

end JacobianChallenge
