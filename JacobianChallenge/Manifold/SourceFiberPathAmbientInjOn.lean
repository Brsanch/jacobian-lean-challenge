/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Generalised injectivity of `sourceFiberPath.ambient` at any `t ∈ Icc 0 1`

`sourceFiberPath_tgt_injOn` proves injectivity of `x ↦ (sourceFiberPath x).tgt`
at `t = 1`. This chip generalises to **any** `t₀ ∈ Icc 0 1`:

```
∀ x₁ x₂ ∈ sourceFiber, ∀ t₀ ∈ Icc 0 1,
  (sourceFiberPath x₁).toPath.extend t₀ = (sourceFiberPath x₂).toPath.extend t₀
    → x₁ = x₂
```

Same proof template as `sourceFiberPath_tgt_injOn`: pass through
`path_lift_eqOn_Icc` applied to the reparametrised path
`β ∘ Real.smoothTransition`. The hypothesis `t₀ ∈ Icc 0 1` is used to
land in the regular-value zone.

The `ambient` and `toPath.extend` levels coincide on `Icc 0 1` via
`ambient_eq_on_unitInterval`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Generalised target-map injectivity on the source fiber.**

If `x₁, x₂ ∈ sourceFiber` produce smooth paths that agree at some
`t₀ ∈ Icc 0 1` (via `toPath.extend`), then `x₁ = x₂`.

Same proof template as `sourceFiberPath_tgt_injOn` (which is the
`t₀ = 1` case), parametrized over `t₀`. -/
theorem sourceFiberPath_toPath_extend_injOn_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x₁ x₂ : X}
    (hx₁ : f.toRiemannSphere x₁ = β 0)
    (hx₂ : f.toRiemannSphere x₂ = β 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (h_agree :
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend t₀
        = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend t₀) :
    x₁ = x₂ := by
  classical
  let sigma : ℝ → ℝ := Real.smoothTransition
  have hσ_range : ∀ t : ℝ, sigma t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  let β' : ℝ → RiemannSphere := fun t => β (sigma t)
  have hβ'_reg : ∀ t ∈ Icc (0 : ℝ) 1, β' t ∈ f.regularValueSet := by
    intro t _
    exact hβ_reg (sigma t) (hσ_range t)
  let γ₁ : ℝ → X :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend
  let γ₂ : ℝ → X :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend
  have hγ₁_cont : Continuous γ₁ :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend.continuous
  have hγ₂_cont : Continuous γ₂ :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend.continuous
  -- Each γᵢ lifts β' on Icc 0 1.
  have hγ₁_lift : ∀ t ∈ Icc (0 : ℝ) 1, f.toRiemannSphere (γ₁ t) = β' t := by
    intro t ht
    show f.toRiemannSphere
      ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend t) = β (sigma t)
    rw [Path.extend_extends'
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath ⟨t, ht⟩]
    exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx₁ ⟨t, ht⟩
  have hγ₂_lift : ∀ t ∈ Icc (0 : ℝ) 1, f.toRiemannSphere (γ₂ t) = β' t := by
    intro t ht
    show f.toRiemannSphere
      ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend t) = β (sigma t)
    rw [Path.extend_extends'
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath ⟨t, ht⟩]
    exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx₂ ⟨t, ht⟩
  -- Apply path_lift_eqOn_Icc at t₀.
  have h_agree' : γ₁ t₀ = γ₂ t₀ := h_agree
  have h_eqOn : Set.EqOn γ₁ γ₂ (Icc (0 : ℝ) 1) :=
    f.path_lift_eqOn_Icc hβ'_reg hγ₁_cont hγ₂_cont
      hγ₁_lift hγ₂_lift ht₀ h_agree'
  -- Evaluate at t = 0.
  have hγ₁_zero : γ₁ 0 = x₁ := by
    show (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend 0 = x₁
    rw [Path.extend_zero]
    exact f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx₁
  have hγ₂_zero : γ₂ 0 = x₂ := by
    show (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend 0 = x₂
    rw [Path.extend_zero]
    exact f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx₂
  have h_zero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have : γ₁ 0 = γ₂ 0 := h_eqOn h_zero_mem
  rw [hγ₁_zero, hγ₂_zero] at this
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
