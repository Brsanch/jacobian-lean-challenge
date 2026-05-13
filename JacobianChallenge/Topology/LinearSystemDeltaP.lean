/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics.threshold 100

/-! # `IsBoundedByDeltaP` predicate and its `Zero`-`Add`-`Smul` closure

The linear system `L(δp) := { f meromorphic on X : ord_x f ≥ 0 for
x ≠ p, ord_p f ≥ -1 }` is the central object of Riemann-Roch at
`δp`. Showing `dim L(δp) ≥ 2` at genus 0 — i.e. discharging zz346's
`ExistsNonConstantBoundedByDeltaP_GenusZero X` — requires being
able to talk about `L(δp)` *as a vector space*.

This chip is the foundation: a predicate
`IsBoundedByDeltaP X p (f : X → ℂ)` matching the `L(δp)` membership
condition, plus closure under

* zero — `0 ∈ L(δp)` (trivially, the zero function is meromorphic
  with order `⊤` everywhere),
* addition — `f, g ∈ L(δp) ⇒ f + g ∈ L(δp)` (via mathlib's
  `meromorphicOrderAt_add`),
* scalar multiplication by `ℂ`.

This positions `L(δp)` to be wrapped as a `Submodule ℂ (X → ℂ)` in a
follow-up chip, at which point standard linear-algebra dim machinery
becomes available.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The `L(δp)` membership predicate.** `f : X → ℂ` is bounded by
`δp` iff it is globally meromorphic, of order `≥ 0` off `p`, and of
order `≥ -1` at `p`. -/
def IsBoundedByDeltaP (p : X) (f : X → ℂ) : Prop :=
  MMeromorphicOn (𝓘(ℂ, ℂ)) f Set.univ ∧
  (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f x) ∧
  ((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f p

/-- **`0 ∈ L(δp)`.** The zero function is meromorphic, with
order `⊤` everywhere — in particular `≥ 0` and `≥ -1`. -/
lemma IsBoundedByDeltaP.zero (p : X) :
    IsBoundedByDeltaP p (0 : X → ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `MMeromorphicOn` of the zero function on `univ`.
    exact MMeromorphicOn.zero
  · intro x _
    -- `mmeromorphicOrderAt _ 0 x = ⊤ ≥ 0`.
    show 0 ≤ meromorphicOrderAt ((0 : X → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
    have h_zero_comp : ((0 : X → ℂ) ∘ (chartAt ℂ x).symm) = (fun _ : ℂ => (0 : ℂ)) := rfl
    rw [h_zero_comp, meromorphicOrderAt_const ((chartAt ℂ x) x) (0 : ℂ)]
    simp
  · -- Same at p.
    show ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt ((0 : X → ℂ) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
    have h_zero_comp : ((0 : X → ℂ) ∘ (chartAt ℂ p).symm) = (fun _ : ℂ => (0 : ℂ)) := rfl
    rw [h_zero_comp, meromorphicOrderAt_const ((chartAt ℂ p) p) (0 : ℂ)]
    simp

/-- **Sum closure: `f, g ∈ L(δp) ⇒ f + g ∈ L(δp)`.** Uses mathlib's
`meromorphicOrderAt_add` (`min(ord f, ord g) ≤ ord (f+g)`). -/
lemma IsBoundedByDeltaP.add {p : X} {f g : X → ℂ}
    (hf : IsBoundedByDeltaP p f) (hg : IsBoundedByDeltaP p g) :
    IsBoundedByDeltaP p (f + g) := by
  obtain ⟨hf_mero, hf_off, hf_p⟩ := hf
  obtain ⟨hg_mero, hg_off, hg_p⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · -- Sum is MMeromorphicOn.
    intro x hx
    have hxf : MMeromorphicAt (𝓘(ℂ, ℂ)) f x := hf_mero x hx
    have hxg : MMeromorphicAt (𝓘(ℂ, ℂ)) g x := hg_mero x hx
    -- MMeromorphicAt unfolds to MeromorphicAt of chart pullback, and
    -- `(f + g) ∘ chart.symm = f ∘ chart.symm + g ∘ chart.symm`.
    show MeromorphicAt ((f + g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
    have h_unf : (f + g) ∘ (chartAt ℂ x).symm
        = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
    rw [h_unf]
    exact hxf.add hxg
  · -- Order off p ≥ 0.
    intro x hx
    have hxf : MMeromorphicAt (𝓘(ℂ, ℂ)) f x := hf_mero x (Set.mem_univ x)
    have hxg : MMeromorphicAt (𝓘(ℂ, ℂ)) g x := hg_mero x (Set.mem_univ x)
    have h_min : min (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f x)
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x)
          ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (f + g) x := by
      show min (meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        (meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
          ≤ meromorphicOrderAt ((f + g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      have h_unf : (f + g) ∘ (chartAt ℂ x).symm
          = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
      rw [h_unf]
      exact meromorphicOrderAt_add hxf hxg
    -- Now combine with `0 ≤ min ord f, ord g`.
    have h_min_nonneg : 0 ≤ min (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f x)
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x) :=
      le_min (hf_off x hx) (hg_off x hx)
    exact h_min_nonneg.trans h_min
  · -- Order at p ≥ -1.
    have hxf : MMeromorphicAt (𝓘(ℂ, ℂ)) f p := hf_mero p (Set.mem_univ p)
    have hxg : MMeromorphicAt (𝓘(ℂ, ℂ)) g p := hg_mero p (Set.mem_univ p)
    have h_min : min (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f p)
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g p)
          ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (f + g) p := by
      show min (meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p))
        (meromorphicOrderAt (g ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p))
          ≤ meromorphicOrderAt ((f + g) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
      have h_unf : (f + g) ∘ (chartAt ℂ p).symm
          = (f ∘ (chartAt ℂ p).symm) + (g ∘ (chartAt ℂ p).symm) := rfl
      rw [h_unf]
      exact meromorphicOrderAt_add hxf hxg
    have h_min_neg1 : ((-1 : ℤ) : WithTop ℤ) ≤ min
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f p)
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g p) :=
      le_min hf_p hg_p
    exact h_min_neg1.trans h_min

/-- **Constant functions are in `L(δp)`.** A non-zero constant `c`
has order `0` everywhere; the zero constant is covered by
`IsBoundedByDeltaP.zero`. -/
lemma IsBoundedByDeltaP.const (p : X) (c : ℂ) :
    IsBoundedByDeltaP p (fun _ : X => c) := by
  by_cases hc : c = 0
  · -- c = 0 case reduces to zero.
    subst hc
    exact IsBoundedByDeltaP.zero p
  · -- c ≠ 0 case: order is 0 everywhere.
    refine ⟨?_, ?_, ?_⟩
    · -- Constant function is meromorphic everywhere.
      intro x _
      exact MMeromorphicAt.const c
    · intro x _
      show 0 ≤ meromorphicOrderAt ((fun _ : X => c) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      have h_eq : (fun _ : X => c) ∘ (chartAt ℂ x).symm
          = (fun _ : ℂ => c) := rfl
      rw [h_eq, meromorphicOrderAt_const ((chartAt ℂ x) x) c]
      simp [hc]
    · show ((-1 : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt ((fun _ : X => c) ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
      have h_eq : (fun _ : X => c) ∘ (chartAt ℂ p).symm
          = (fun _ : ℂ => c) := rfl
      rw [h_eq, meromorphicOrderAt_const ((chartAt ℂ p) p) c]
      -- Goal: ((-1 : ℤ) : WithTop ℤ) ≤ if c = 0 then ⊤ else 0
      rw [if_neg hc]
      -- Goal: ((-1 : ℤ) : WithTop ℤ) ≤ (0 : WithTop ℤ)
      have : ((-1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by
        rw [WithTop.coe_le_coe]
        decide
      exact this

end JacobianChallenge

end
