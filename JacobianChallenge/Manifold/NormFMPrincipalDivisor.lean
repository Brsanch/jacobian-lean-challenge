/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Jacobian
import JacobianChallenge.Manifold.NormFMUnconditional
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Pointwise norm-divisor identity

For non-constant `f : X → Y` between compact Riemann surfaces and
`g : MeromorphicNonzero X`, the pushforward of the principal divisor of
`g` along `f` agrees pointwise with the principal divisor of `NormFM f g`:

```
((divPushforwardHom f (principalDivisorMap g) : Div Y) : Y → ℤ) y₀
  = (mmeromorphicOrderAt 𝓘(ℂ, ℂ) (NormFM f hf hnc g) y₀).untop₀
```

P1.3 (the divisor-level identity) follows by `DFunLike.ext`.
-/

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Pointwise Norm-Divisor identity** at `y₀ : Y`. -/
theorem divPushforwardHom_principalDivisor_eq_NormFM_orderFun
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : JacobianChallenge.MeromorphicNonzero X) (y₀ : Y) :
    ((JacobianChallenge.Pic0.divPushforwardHom f
        (JacobianChallenge.principalDivisorMap g) : JacobianChallenge.Div Y)
        : Y → ℤ) y₀
      = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (NormFM f hf hnc g) y₀).untop₀ := by
  classical
  obtain ⟨FF, h_fibre, h_full_fibre, h_RHS_eq⟩ :=
    NormFM_principalDivisor_apply_at_y₀ hf hnc g y₀
  rw [h_RHS_eq]
  -- Goal: ((divPushforwardHom f (principalDivisorMap g)) : Y → ℤ) y₀
  --     = ∑ x ∈ FF.attach, (mmero g x.val).untop₀
  show ((JacobianChallenge.Div.singletonMap f
          (JacobianChallenge.principalDivisorMap g)) : Y → ℤ) y₀
        = ∑ x ∈ FF.attach,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x.val).untop₀
  rw [show ((JacobianChallenge.Div.singletonMap f
              (JacobianChallenge.principalDivisorMap g)) : Y → ℤ) y₀
        = ∑ x ∈ (JacobianChallenge.principalDivisorMap g).supportFinset,
          ((JacobianChallenge.principalDivisorMap g) : X → ℤ) x
            * (if y₀ = f x then 1 else 0) from
      JacobianChallenge.Div.singletonMapFun_apply f
        (JacobianChallenge.principalDivisorMap g) y₀]
  -- Convert ∑ x ∈ FF.attach to ∑ x ∈ FF.
  rw [Finset.sum_attach FF
      (fun x => (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x).untop₀)]
  -- Use principalDivisorMap_apply pointwise.
  have h_pdm : ∀ x : X, ((JacobianChallenge.principalDivisorMap g) : X → ℤ) x
      = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x).untop₀ := by
    intro x; rfl
  simp_rw [h_pdm]
  -- LHS: ∑ x ∈ supp(pdm).toFinset, (mmero g x).untop₀ * (if y₀ = f x then 1 else 0)
  -- RHS: ∑ x ∈ FF, (mmero g x).untop₀.
  -- Step A: rewrite indicator * value as conditional value, then collect via sum_filter.
  rw [show (∑ x ∈ (JacobianChallenge.principalDivisorMap g).supportFinset,
            (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x).untop₀
              * (if y₀ = f x then (1 : ℤ) else 0))
        = ∑ x ∈ (JacobianChallenge.principalDivisorMap g).supportFinset,
            (if y₀ = f x
              then (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x).untop₀ else 0) from
      Finset.sum_congr rfl (fun x _ => by
        by_cases h : y₀ = f x <;> simp [h])]
  -- Step B: collect indicator into a filter.
  rw [← Finset.sum_filter]
  -- L ⊆ FF: for x ∈ L, x ∈ supp ∧ y₀ = f x; so f x = y₀, hence x ∈ FF.
  have hL_sub_FF :
      (JacobianChallenge.principalDivisorMap g).supportFinset.filter
        (fun x => y₀ = f x) ⊆ FF := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact h_full_fibre x hx.2.symm
  -- For x ∈ FF \ L: (mmero g x).untop₀ = 0.
  have hFF_minus_L_zero : ∀ x ∈ FF,
      x ∉ (JacobianChallenge.principalDivisorMap g).supportFinset.filter
            (fun x => y₀ = f x) →
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x).untop₀ = 0 := by
    intro x hx_FF hx_notL
    rw [Finset.mem_filter, not_and_or] at hx_notL
    rcases hx_notL with h_notSupp | h_neq
    · have h_zero : ((JacobianChallenge.principalDivisorMap g) : X → ℤ) x = 0 :=
        JacobianChallenge.Div.apply_eq_zero_of_notMem_supportFinset h_notSupp
      -- principalDivisorMap_apply: pdm g x = (mmero g x).untop₀.
      rw [← h_pdm x]; exact h_zero
    · have : f x = y₀ := h_fibre x hx_FF
      exact absurd this.symm h_neq
  -- Now: ∑ x ∈ L, (mmero g x).untop₀ = ∑ x ∈ FF, (mmero g x).untop₀ via sum_subset.
  exact Finset.sum_subset hL_sub_FF hFF_minus_L_zero

/-- **Nonvanishing germ of `NormFM`.** For non-constant `f` and
`g : MeromorphicNonzero X`, the pushed-down norm `NormFM f hf hnc g` has
no germ identically zero at any `y₀ : Y`.

Proof: if `mmeromorphicOrderAt I (NormFM f hf hnc g) y₀ = ⊤`, the
fibre-sum identity forces `∑_{x ∈ fibre} mmero(g, x) = ⊤`, which by
`WithTop.sum_eq_top` requires some `mmero(g, x) = ⊤` — contradicting
`g.nonvanishing_germ`. -/
theorem NormFM_nonvanishing_germ
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : JacobianChallenge.MeromorphicNonzero X) :
    ∀ y₀ : Y, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (NormFM f hf hnc g) y₀ ≠ ⊤ := by
  intro y₀ h_top
  obtain ⟨FF, _h_fibre, h_eq⟩ :=
    NormFM_mmeromorphicOrderAt_eq_fibre_sum hf hnc g y₀
  rw [h_top] at h_eq
  -- h_eq : ⊤ = ∑ x ∈ FF.attach, mmero(g, x.val).
  have h_sum_top :
      (∑ x ∈ FF.attach, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g.toFun x.val) = ⊤ :=
    h_eq.symm
  rw [WithTop.sum_eq_top] at h_sum_top
  obtain ⟨x, _hx_mem, hx_top⟩ := h_sum_top
  exact g.nonvanishing_germ x.val hx_top

end Manifold
end JacobianChallenge
