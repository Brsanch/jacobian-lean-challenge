/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Target-map injectivity for `sourceFiberPath`

The map `x ↦ (sourceFiberPath x).tgt : sourceFiber → X` is **injective**.
This is the foundational bijection-content underlying the upcoming
identification `boundary(levelSetChain) = principalDivisorMap f` (step 7
proper) — different zeros of `f` lift along `β` to different poles.

## Argument

For `x₁, x₂ ∈ sourceFiber` with shared target `y`:

* Extend each `(sourceFiberPath xᵢ).toPath` to a continuous map
  `extᵢ : ℝ → X` via `Path.extend`, which is identity on `Icc 0 1`
  and clamps outside.
* On `Icc 0 1`, `extᵢ` agrees with `(sourceFiberPath xᵢ).toPath`, so:
  - `extᵢ 0 = xᵢ` (source);
  - `extᵢ 1 = y` (target — same for both);
  - `f.toRiemannSphere (extᵢ t) = β (Real.smoothTransition t)` for
    `t ∈ Icc 0 1` (via `sourceFiberPath_toPath_lifts` + `extend_extends'`).
* Applying `path_lift_eqOn_Icc` to the lifted path `β ∘ Real.smoothTransition`
  on `Icc 0 1` (which takes regular values, since `σ([0,1]) ⊆ [0,1]`)
  at `t₀ = 1` (where `ext₁ 1 = ext₂ 1 = y`), we get `ext₁ = ext₂` on
  `Icc 0 1`. Evaluating at `t = 0` gives `x₁ = x₂`.

## What ships

* `MeromorphicNonzero.sourceFiberPath_tgt_injOn` — `Set.InjOn`-form of
  target injectivity, restricted to the source fiber.

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

/-- **Target-map injectivity on the source fiber.**

If `x₁, x₂ ∈ sourceFiber` produce smooth paths with the same target,
then `x₁ = x₂`. The proof routes through `path_lift_eqOn_Icc` applied
to the reparametrised path `β ∘ Real.smoothTransition`. -/
theorem sourceFiberPath_tgt_injOn
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x₁ x₂ : X}
    (hx₁ : f.toRiemannSphere x₁ = β 0)
    (hx₂ : f.toRiemannSphere x₂ = β 0)
    (h_tgt :
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).tgt
        = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).tgt) :
    x₁ = x₂ := by
  classical
  -- Set up the reparametrised path β' := β ∘ Real.smoothTransition.
  let sigma : ℝ → ℝ := Real.smoothTransition
  have hσ_range : ∀ t : ℝ, sigma t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  let β' : ℝ → RiemannSphere := fun t => β (sigma t)
  -- β' takes regular values on Icc 0 1.
  have hβ'_reg : ∀ t ∈ Icc (0 : ℝ) 1, β' t ∈ f.regularValueSet := by
    intro t _
    exact hβ_reg (sigma t) (hσ_range t)
  -- Extend each toPath to a continuous map ℝ → X.
  let γ₁ : ℝ → X :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend
  let γ₂ : ℝ → X :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend
  have hγ₁_cont : Continuous γ₁ :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend.continuous
  have hγ₂_cont : Continuous γ₂ :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend.continuous
  -- Each γᵢ lifts β' on Icc 0 1.
  have hγ_lifts :
      ∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
        f.toRiemannSphere ((![γ₁, γ₂] i) t) = β' t := by
    intro i t ht
    -- For t ∈ Icc 0 1, the extend agrees with toPath.
    have h_in_I : t ∈ (Icc 0 1 : Set ℝ) := ht
    -- For each i, γᵢ t = (toPath_i) ⟨t, ht⟩, then lifts to β (σ t).
    fin_cases i
    · show f.toRiemannSphere (γ₁ t) = β' t
      show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend t) = β (sigma t)
      rw [Path.extend_extends'
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath ⟨t, h_in_I⟩]
      exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx₁ ⟨t, h_in_I⟩
    · show f.toRiemannSphere (γ₂ t) = β' t
      show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend t) = β (sigma t)
      rw [Path.extend_extends'
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath ⟨t, h_in_I⟩]
      exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx₂ ⟨t, h_in_I⟩
  have hγ₁_lift : ∀ t ∈ Icc (0 : ℝ) 1, f.toRiemannSphere (γ₁ t) = β' t :=
    hγ_lifts 0
  have hγ₂_lift : ∀ t ∈ Icc (0 : ℝ) 1, f.toRiemannSphere (γ₂ t) = β' t :=
    hγ_lifts 1
  -- γᵢ 1 = .tgt; hypothesis: targets equal.
  have hγ₁_one : γ₁ 1 = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).tgt :=
    Path.extend_one _
  have hγ₂_one : γ₂ 1 = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).tgt :=
    Path.extend_one _
  have h_agree_at_one : γ₁ 1 = γ₂ 1 := by
    rw [hγ₁_one, hγ₂_one, h_tgt]
  -- Apply path_lift_eqOn_Icc with β' on Icc 0 1, at t₀ = 1.
  have h_one_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have h_eqOn : Set.EqOn γ₁ γ₂ (Icc (0 : ℝ) 1) :=
    f.path_lift_eqOn_Icc hβ'_reg hγ₁_cont hγ₂_cont
      hγ₁_lift hγ₂_lift h_one_mem h_agree_at_one
  -- Evaluate at t = 0: γᵢ 0 = .src = xᵢ.
  have hγ₁_zero : γ₁ 0 = x₁ := by
    rw [show γ₁ 0 = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₁).toPath.extend 0
        from rfl, Path.extend_zero]
    exact f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx₁
  have hγ₂_zero : γ₂ 0 = x₂ := by
    rw [show γ₂ 0 = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx₂).toPath.extend 0
        from rfl, Path.extend_zero]
    exact f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx₂
  have h_zero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have : γ₁ 0 = γ₂ 0 := h_eqOn h_zero_mem
  rw [hγ₁_zero, hγ₂_zero] at this
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
