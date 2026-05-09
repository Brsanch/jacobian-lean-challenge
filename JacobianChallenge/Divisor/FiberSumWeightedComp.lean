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

end Div

end JacobianChallenge
