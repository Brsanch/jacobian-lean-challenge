/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetTargetFiber
import JacobianChallenge.Manifold.MeromorphicNonzeroPrincipalDivisorAtPole
import JacobianChallenge.Manifold.MeromorphicNonzeroPrincipalDivisorAtZero
import JacobianChallenge.Manifold.MeromorphicNonzeroPrincipalDivisorOffFiber

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Step 7d-d — pointwise identification with `−principalDivisorMap f`

Under the hypothesis that `β 0 = ↑0` (start at a simple zero) and
`β 1 = ∞` (end at a simple pole) with regular values on `Icc 0 1`,
the boundary of the level-set chain equals `−principalDivisorMap f`
*pointwise*:

  `∀ x : X, (∂ levelSetChain).toFun x = −(principalDivisorMap f).toFun x`.

This combines 7d-a (off-fiber → 0), 7d-b (zero → 1), 7d-c (pole → -1)
with the fiber-form boundary `boundary_levelSetChain_eq_fiberDiff`
(step 7c).

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Pointwise identification of boundary with `−principalDivisorMap f`.**

Under `β 0 = ↑0`, `β 1 = ∞`, and regular values on `Icc 0 1`, the
boundary `∂ levelSetChain` evaluated at any `x : X` equals
`−(principalDivisorMap f).toFun x`. -/
theorem boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (hβ_zero : β 0 = (((0 : ℂ) : RiemannSphere)))
    (hβ_one : β 1 = (OnePoint.infty : RiemannSphere)) :
    ∀ x : X,
      (SmoothChain.boundary (f.levelSetChain hnc hβ_smooth hβ_reg)).toFun x
        = -((principalDivisorMap f : X → ℤ) x) := by
  intro x
  -- Unfold boundary via step 7c.
  rw [f.boundary_levelSetChain_eq_fiberDiff hnc hβ_smooth hβ_reg]
  -- Now LHS = (Σ target Fsinsupp - Σ source Fsinsupp).toFun x.
  -- Evaluate the Finsupp sum pointwise.
  have hβ0_reg : β 0 ∈ f.regularValueSet :=
    hβ_reg 0 ⟨le_refl _, by norm_num⟩
  have hβ1_reg : β 1 ∈ f.regularValueSet :=
    hβ_reg 1 ⟨by norm_num, le_refl _⟩
  -- Helper: evaluate Σ Finsupp.single y 1 at x = [x ∈ Finset].
  have h_sum_eval : ∀ (S : Finset X),
      ((∑ y ∈ S, Finsupp.single y (1 : ℤ)) : X →₀ ℤ) x
        = if x ∈ S then 1 else 0 := by
    intro S
    rw [Finsupp.coe_finset_sum]
    simp only [Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' S x (fun _ => (1 : ℤ))]
  -- Source and target Finsupp values (transferred via toFun = coe).
  have h_source_val :
      ((∑ y ∈ f.sourceFiber hβ0_reg, Finsupp.single y (1 : ℤ)) : X →₀ ℤ) x
        = if x ∈ f.sourceFiber hβ0_reg then 1 else 0 := h_sum_eval _
  have h_target_val :
      ((∑ y ∈ f.targetFiber hβ1_reg, Finsupp.single y (1 : ℤ)) : X →₀ ℤ) x
        = if x ∈ f.targetFiber hβ1_reg then 1 else 0 := h_sum_eval _
  -- Combine.
  show ((∑ y ∈ f.targetFiber hβ1_reg, Finsupp.single y (1 : ℤ))
      - (∑ x_1 ∈ f.sourceFiber hβ0_reg, Finsupp.single x_1 (1 : ℤ))).toFun x
      = -((principalDivisorMap f : X → ℤ) x)
  change ((∑ y ∈ f.targetFiber hβ1_reg, Finsupp.single y (1 : ℤ))
      - (∑ x_1 ∈ f.sourceFiber hβ0_reg, Finsupp.single x_1 (1 : ℤ)) : X →₀ ℤ) x
      = -((principalDivisorMap f : X → ℤ) x)
  rw [Finsupp.sub_apply, h_target_val, h_source_val]
  -- Case split: x ∈ sourceFiber, x ∈ targetFiber, or neither.
  by_cases h_src : x ∈ f.sourceFiber hβ0_reg
  · -- x is a zero. (principalDivisorMap f).toFun x = 1.
    -- f.toRS x = β 0 = some 0.
    have h_toRS_x : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere)) := by
      have : f.toRiemannSphere x = β 0 :=
        (f.mem_sourceFiber_iff hβ0_reg x).mp h_src
      rw [this, hβ_zero]
    -- x is regular (preimage of regular value).
    have hx_reg : x ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue (hβ_zero ▸ hβ0_reg) h_toRS_x
    have h_pdiv : (principalDivisorMap f : X → ℤ) x = 1 :=
      f.principalDivisorMap_toFun_eq_one_at_simple_zero hnc h_toRS_x hx_reg
    -- x ∉ targetFiber (x is a zero, not pole — these are disjoint).
    have h_not_tgt : x ∉ f.targetFiber hβ1_reg := by
      intro h_tgt
      have h_toRS_x_inf : f.toRiemannSphere x = β 1 :=
        (f.mem_targetFiber_iff hβ1_reg x).mp h_tgt
      rw [hβ_one] at h_toRS_x_inf
      rw [h_toRS_x] at h_toRS_x_inf
      exact OnePoint.coe_ne_infty _ h_toRS_x_inf
    rw [if_pos h_src, if_neg h_not_tgt, h_pdiv]
    ring
  · by_cases h_tgt : x ∈ f.targetFiber hβ1_reg
    · -- x is a pole. (principalDivisorMap f).toFun x = -1.
      have h_toRS_x : f.toRiemannSphere x = (OnePoint.infty : RiemannSphere) := by
        have : f.toRiemannSphere x = β 1 :=
          (f.mem_targetFiber_iff hβ1_reg x).mp h_tgt
        rw [this, hβ_one]
      have hx_reg : x ∈ f.regularSet :=
        f.mem_regularSet_of_preimage_regularValue (hβ_one ▸ hβ1_reg) h_toRS_x
      have h_pdiv : (principalDivisorMap f : X → ℤ) x = -1 :=
        f.principalDivisorMap_toFun_eq_neg_one_at_simple_pole hnc h_toRS_x hx_reg
      rw [if_neg h_src, if_pos h_tgt, h_pdiv]
      ring
    · -- x is neither. (principalDivisorMap f).toFun x = 0.
      have h_not_zero : f.toRiemannSphere x ≠ (((0 : ℂ) : RiemannSphere)) := by
        intro h_eq
        apply h_src
        rw [f.mem_sourceFiber_iff hβ0_reg, hβ_zero]
        exact h_eq
      have h_not_pole : f.toRiemannSphere x ≠ (OnePoint.infty : RiemannSphere) := by
        intro h_eq
        apply h_tgt
        rw [f.mem_targetFiber_iff hβ1_reg, hβ_one]
        exact h_eq
      have h_pdiv : (principalDivisorMap f : X → ℤ) x = 0 :=
        f.principalDivisorMap_toFun_eq_zero_off_fiber x h_not_zero h_not_pole
      rw [if_neg h_src, if_neg h_tgt, h_pdiv]
      ring

end MeromorphicNonzero

end JacobianChallenge

end
