/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftSmoothOnIcc
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.ComplexManifoldRealification
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # SmoothPath bundle from the smooth path lift on `Icc 0 1`

Wraps the smooth path lift produced by `exists_contMDiffOn_lift_on_Icc`
(steps 1–3 of the C3 staircase) into a `SmoothPath 𝓘(ℝ, ℂ) X`.

The smoothness witness in `SmoothPath` requires a **globally** `C^∞`
function `f : ℝ → X` (not just on `Icc 0 1`). We achieve this by
reparametrising the lift via `Real.smoothTransition`:

* `σ := Real.smoothTransition : ℝ → ℝ` is `C^∞` with `σ ⁰t⁰ = 0`,
  `σ ¹t¹ = 1`, and range `[0, 1]` (`smoothTransition.zero_of_nonpos`,
  `_.one_of_one_le`, and `_.continuous` bounds — all `[0, 1]` on ℝ).
* `γ_smooth := γ ∘ σ` is then defined on all of `ℝ`. Since `σ(t) ∈ [0, 1]`
  for every `t` and `γ` is `ContMDiffOn ∞` on `[0, 1]`, the composition
  is `ContMDiff ∞` globally via `ContMDiffOn.comp_contMDiff`.
* `toPath := Path.mk ⟨γ_smooth ∘ Subtype.val, ...⟩` with endpoints
  `γ 0 = x₀` and `γ 1`. The reparametrisation makes `toPath t.val =
  γ_smooth t.val = γ (σ t.val)` for `t : unitInterval`.

## What ships

* `MeromorphicNonzero.exists_smoothPath_of_lift_on_unitInterval` —
  given `C^∞` `β` taking regular values on `unitInterval` and `x₀`
  over `β 0`, produces `γ : SmoothPath 𝓘(ℝ, ℂ) X` with `γ.src = x₀`,
  `f.toRiemannSphere γ.tgt = β 1`, and the underlying path lifts `β`
  on `unitInterval` (modulo the smooth-transition reparametrisation).

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff Unit unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **SmoothPath bundle from a smooth path lift on the unit interval.**

Given a `C^∞` path `β : ℝ → RiemannSphere` whose values on `Icc 0 1`
are all regular for `f`, and a preimage `x₀` of `β 0`, there is a
`SmoothPath 𝓘(ℝ, ℂ) X` from `x₀` to some preimage of `β 1`. The
underlying continuous path lifts `β` after reparametrisation by
`Real.smoothTransition`. -/
theorem exists_smoothPath_of_lift_on_unitInterval
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β) (x₀ : X)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    (hx₀ : f.toRiemannSphere x₀ = β 0) :
    ∃ γ : SmoothPath 𝓘(ℝ, ℂ) X,
      γ.src = x₀ ∧
      f.toRiemannSphere γ.tgt = β 1 ∧
      ∀ t : unitInterval,
        f.toRiemannSphere (γ.toPath t) = β (Real.smoothTransition t.val) := by
  classical
  -- Step 3 supplies a continuous γ_raw : ℝ → X that's ContMDiffOn ∞ on Icc 0 1.
  obtain ⟨γ_raw, hγ_cont, hγ_smooth_on, hγ_zero, hγ_lift⟩ :=
    f.exists_contMDiffOn_lift_on_Icc hnc hβ_smooth x₀ hβ_reg hx₀ (by norm_num : (0:ℝ) ≤ 1)
  -- sigma := Real.smoothTransition, C^∞ with range [0, 1], σ 0 = 0, σ 1 = 1.
  let sigma : ℝ → ℝ := Real.smoothTransition
  have hσ_contDiff : ContDiff ℝ ∞ sigma := Real.smoothTransition.contDiff
  have hσ_contMDiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ sigma := hσ_contDiff.contMDiff
  have hσ_range : ∀ t : ℝ, sigma t ∈ Icc (0 : ℝ) 1 := by
    intro t
    refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hσ_zero : sigma 0 = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  have hσ_one : sigma 1 = 1 := Real.smoothTransition.one_of_one_le le_rfl
  -- γ_smooth := γ_raw ∘ sigma : ℝ → X, ContMDiff ∞ globally.
  let γ_smooth : ℝ → X := γ_raw ∘ sigma
  have hγ_smooth_contMDiff :
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ_smooth :=
    hγ_smooth_on.comp_contMDiff hσ_contMDiff hσ_range
  have hγ_smooth_cont : Continuous γ_smooth := hγ_smooth_contMDiff.continuous
  -- γ_smooth 0 = x₀.
  have hγ_smooth_zero : γ_smooth 0 = x₀ := by
    show γ_raw (sigma 0) = x₀
    rw [hσ_zero, hγ_zero]
  -- γ_smooth 1 = γ_raw 1.
  have hγ_smooth_one_eq : γ_smooth 1 = γ_raw 1 := by
    show γ_raw (sigma 1) = γ_raw 1
    rw [hσ_one]
  -- f.toRS (γ_raw 1) = β 1.
  have h_fγ1 : f.toRiemannSphere (γ_raw 1) = β 1 :=
    hγ_lift 1 ⟨by norm_num, le_refl _⟩
  -- Underlying Path for SmoothPath: t ↦ γ_smooth t.val on unitInterval.
  -- Endpoints: γ_smooth 0 = x₀ and γ_smooth 1 = γ_raw 1.
  let pathFun : unitInterval → X := fun t => γ_smooth t.val
  have hpathFun_cont : Continuous pathFun :=
    hγ_smooth_cont.comp continuous_subtype_val
  have hpathFun_zero : pathFun 0 = x₀ := by
    show γ_smooth (0 : unitInterval).val = x₀
    change γ_smooth 0 = x₀
    exact hγ_smooth_zero
  have hpathFun_one : pathFun 1 = γ_raw 1 := by
    show γ_smooth (1 : unitInterval).val = γ_raw 1
    change γ_smooth 1 = γ_raw 1
    exact hγ_smooth_one_eq
  -- Build the Path.
  let toPath : Path x₀ (γ_raw 1) :=
    { toFun := pathFun
      continuous_toFun := hpathFun_cont
      source' := hpathFun_zero
      target' := hpathFun_one }
  -- The underlying Path lifts β ∘ Real.smoothTransition on unitInterval.
  have h_toPath_lifts : ∀ t : unitInterval,
      f.toRiemannSphere (toPath t) = β (Real.smoothTransition t.val) := by
    intro t
    -- toPath t = pathFun t = γ_smooth t.val = γ_raw (sigma t.val).
    show f.toRiemannSphere (γ_raw (sigma t.val)) = β (Real.smoothTransition t.val)
    -- γ_raw lifts β on Icc 0 1, sigma t.val ∈ Icc 0 1.
    exact hγ_lift (sigma t.val) (hσ_range t.val)
  -- Assemble SmoothPath.
  refine ⟨{
    src := x₀
    tgt := γ_raw 1
    toPath := toPath
    smooth := ⟨γ_smooth, hγ_smooth_contMDiff, ?_⟩
  }, rfl, h_fγ1, h_toPath_lifts⟩
  -- f t.val = toPath t for t : unitInterval, where the field f here is γ_smooth.
  intro t
  -- toPath t = pathFun t = γ_smooth t.val.
  show γ_smooth t.val = (toPath : unitInterval → X) t
  rfl

end MeromorphicNonzero

end JacobianChallenge

end
