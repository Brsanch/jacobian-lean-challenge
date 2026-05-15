/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetTargetInjective
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Target-map surjectivity onto the target fiber

For `β` smooth and regular on `Icc 0 1`, every `y ∈ f.toRiemannSphere ⁻¹' {β 1}`
arises as the target of some `sourceFiberPath x` with `x` in the
source fiber. Combined with the injectivity (7a), this gives the
target-map bijection between `sourceFiber` and `targetFiber`.

## Argument

Given `y` with `f.toRiemannSphere y = β 1`:

* Build the time-reversed path `β_rev(t) := β (1 - t)`. It is `C^∞`
  globally (composition with the affine `t ↦ 1 - t`).
* `β_rev` takes regular values on `Icc 0 1` (since `t ∈ [0, 1] ⇒
  1 - t ∈ [0, 1]`).
* Apply `exists_smoothPath_of_lift_on_unitInterval` to `β_rev` at
  `y` (which lifts `β_rev 0 = β 1`). Get `back_path` with
  `back_path.src = y` and `f.toRiemannSphere back_path.tgt = β_rev 1 = β 0`.
* Set `x := back_path.tgt`. By construction `x` is in the source fiber.
* Apply `exists_continuous_lift_on_Icc` to `(β, x)` to get a raw
  continuous lift `γ_raw : ℝ → X` of `β` on `Icc 0 1` with
  `γ_raw 0 = x`.
* The time-reversal of `back_path.toPath.extend` is a continuous lift
  of `β ∘ τ` on `Icc 0 1` (where `τ(t) = 1 - Real.smoothTransition (1 - t)`)
  starting at `x`. So is `γ_raw ∘ τ`. By `path_lift_eqOn_Icc` on
  `β ∘ τ` (regular on `[0, 1]` since `τ([0, 1]) ⊆ [0, 1]`), they
  agree on `Icc 0 1`. Evaluating at `t = 1`: `back_path.toPath.extend 0 =
  γ_raw (τ 1) = γ_raw 1`, i.e., `y = γ_raw 1`.
* Similarly `(sourceFiberPath x).toPath.extend` lifts `β ∘
  Real.smoothTransition` on `Icc 0 1` starting at `x`. So does
  `γ_raw ∘ Real.smoothTransition`. By `path_lift_eqOn_Icc` they agree
  on `Icc 0 1`. Evaluating at `t = 1`: `(sourceFiberPath x).tgt =
  γ_raw 1`.
* Combine: `(sourceFiberPath x).tgt = y`.

## What ships

* `MeromorphicNonzero.sourceFiberPath_tgt_surjOn` — surjectivity:
  `∀ y, f.toRiemannSphere y = β 1 → ∃ x, f.toRiemannSphere x = β 0 ∧
   (sourceFiberPath x).tgt = y`.

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

/-- **Surjectivity of the target map onto `f.toRiemannSphere ⁻¹' {β 1}`.**

Every preimage of `β 1` arises as the target of some `sourceFiberPath x`
with `x` in the source fiber. -/
theorem sourceFiberPath_tgt_surjOn
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {y : X} (hy : f.toRiemannSphere y = β 1) :
    ∃ (x : X) (hx : f.toRiemannSphere x = β 0),
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).tgt = y := by
  classical
  -- Set up β_rev := β ∘ (1 - ·).
  let neg_shift : ℝ → ℝ := fun t => 1 - t
  have h_neg_shift_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ neg_shift := by
    have : ContDiff ℝ ∞ neg_shift :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ))).sub contDiff_id
    exact this.contMDiff
  let β_rev : ℝ → RiemannSphere := fun t => β (1 - t)
  have hβ_rev_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β_rev :=
    hβ_smooth.comp h_neg_shift_smooth
  have hβ_rev_reg : ∀ t ∈ Icc (0 : ℝ) 1, β_rev t ∈ f.regularValueSet := by
    intro t ht
    have h_1_minus_t : 1 - t ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact hβ_reg (1 - t) h_1_minus_t
  -- β_rev 0 = β 1, β_rev 1 = β 0.
  have hβ_rev_zero : β_rev 0 = β 1 := by show β (1 - 0) = β 1; norm_num
  have hβ_rev_one : β_rev 1 = β 0 := by show β (1 - 1) = β 0; norm_num
  have hy_lift_rev : f.toRiemannSphere y = β_rev 0 := by rw [hβ_rev_zero]; exact hy
  -- Step 4 applied to β_rev at y gives back_path.
  obtain ⟨back_path, h_back_src, h_back_tgt_lift, h_back_toPath_lifts⟩ :=
    f.exists_smoothPath_of_lift_on_unitInterval hnc hβ_rev_smooth y hβ_rev_reg hy_lift_rev
  -- x := back_path.tgt. Then f.toRS x = β_rev 1 = β 0.
  set x : X := back_path.tgt with hx_def
  have hx_lift : f.toRiemannSphere x = β 0 := by
    show f.toRiemannSphere back_path.tgt = β 0
    rw [h_back_tgt_lift, hβ_rev_one]
  -- Step 2 (exists_continuous_lift_on_Icc) for (β, x) gives γ_raw.
  obtain ⟨γ_raw, hγ_cont, hγ_zero, hγ_lift⟩ :=
    f.exists_continuous_lift_on_Icc hnc hβ_smooth.continuous x hβ_reg hx_lift
      (by norm_num : (0:ℝ) ≤ 1)
  -- The forward `sourceFiberPath x` (which we want to show targets `y`).
  let fwd_path := f.sourceFiberPath hnc hβ_smooth hβ_reg hx_lift
  have h_fwd_src : fwd_path.src = x :=
    f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx_lift
  -- sigma := Real.smoothTransition.
  let sigma : ℝ → ℝ := Real.smoothTransition
  have hσ_contDiff : ContDiff ℝ ∞ sigma := Real.smoothTransition.contDiff
  have hσ_cont : Continuous sigma := hσ_contDiff.continuous
  have hσ_range : ∀ t : ℝ, sigma t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hσ_zero : sigma 0 = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  have hσ_one : sigma 1 = 1 := Real.smoothTransition.one_of_one_le le_rfl
  -- τ(t) := 1 - sigma(1 - t). τ(0) = 0, τ(1) = 1, τ([0,1]) ⊆ [0,1].
  let tau : ℝ → ℝ := fun t => 1 - sigma (1 - t)
  have hτ_cont : Continuous tau := by
    continuity
  have hτ_zero : tau 0 = 0 := by show 1 - sigma (1 - 0) = 0; simp [hσ_one]
  have hτ_one : tau 1 = 1 := by show 1 - sigma (1 - 1) = 1; simp [hσ_zero]
  have hτ_range : ∀ t ∈ Icc (0 : ℝ) 1, tau t ∈ Icc (0 : ℝ) 1 := by
    intro t _
    have := hσ_range (1 - t)
    refine ⟨by linarith [this.2], by linarith [this.1]⟩
  -- Both γ_raw ∘ τ and back_path.toPath.extend ∘ (1 - ·) lift β ∘ τ on [0, 1].
  -- Common pattern: β ∘ τ takes regular values on [0, 1].
  have hβτ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β (tau t) ∈ f.regularValueSet := by
    intro t ht
    exact hβ_reg (tau t) (hτ_range t ht)
  have hβσ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β (sigma t) ∈ f.regularValueSet := by
    intro t _
    exact hβ_reg (sigma t) (hσ_range t)
  -- back_path_rev(t) := back_path.toPath.extend(1 - t). Continuous globally.
  let back_path_rev : ℝ → X := fun t => back_path.toPath.extend (1 - t)
  have h_back_rev_cont : Continuous back_path_rev := by
    refine back_path.toPath.extend.continuous.comp ?_
    continuity
  -- back_path_rev 0 = back_path.toPath.extend 1 = back_path.tgt = x.
  have h_back_rev_zero : back_path_rev 0 = x := by
    show back_path.toPath.extend (1 - 0) = x
    rw [show (1 : ℝ) - 0 = 1 from by norm_num, Path.extend_one, hx_def]
  -- back_path_rev 1 = back_path.toPath.extend 0 = back_path.src = y.
  have h_back_rev_one : back_path_rev 1 = y := by
    show back_path.toPath.extend (1 - 1) = y
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, Path.extend_zero, h_back_src]
  -- back_path_rev lifts β ∘ τ on Icc 0 1.
  have h_back_rev_lift : ∀ t ∈ Icc (0 : ℝ) 1,
      f.toRiemannSphere (back_path_rev t) = β (tau t) := by
    intro t ht
    -- back_path_rev t = back_path.toPath.extend (1 - t).
    -- For 1 - t ∈ Icc 0 1, extend ≡ toPath at 1 - t (as a unitInterval element).
    have h_1_minus_t : 1 - t ∈ (Icc (0 : ℝ) 1 : Set ℝ) := by
      refine ⟨by linarith [ht.2], by linarith [ht.1]⟩
    show f.toRiemannSphere (back_path.toPath.extend (1 - t)) = β (tau t)
    rw [Path.extend_extends' back_path.toPath ⟨1 - t, h_1_minus_t⟩]
    -- f.toRS (back_path.toPath ⟨1 - t, _⟩) = β_rev (σ (1 - t)) = β (1 - σ (1 - t)) = β (τ t).
    have := h_back_toPath_lifts ⟨1 - t, h_1_minus_t⟩
    show f.toRiemannSphere (back_path.toPath ⟨1 - t, h_1_minus_t⟩)
      = β (1 - sigma (1 - t))
    exact this
  -- γ_raw ∘ τ lifts β ∘ τ on Icc 0 1.
  have h_γ_τ_lift : ∀ t ∈ Icc (0 : ℝ) 1,
      f.toRiemannSphere (γ_raw (tau t)) = β (tau t) := by
    intro t ht
    exact hγ_lift (tau t) (hτ_range t ht)
  -- γ_raw ∘ τ is continuous globally.
  have h_γ_τ_cont : Continuous (fun t => γ_raw (tau t)) :=
    hγ_cont.comp hτ_cont
  -- Agreement at t = 0: back_path_rev 0 = x = γ_raw 0 = γ_raw (τ 0).
  have h_agree_at_zero : back_path_rev 0 = γ_raw (tau 0) := by
    rw [hτ_zero, hγ_zero, h_back_rev_zero]
  -- Apply path_lift_eqOn_Icc to β ∘ τ on Icc 0 1 at t₀ = 0.
  have h_zero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have h_back_rev_eqOn :
      Set.EqOn back_path_rev (fun t => γ_raw (tau t)) (Icc (0 : ℝ) 1) :=
    f.path_lift_eqOn_Icc hβτ_reg h_back_rev_cont h_γ_τ_cont
      h_back_rev_lift h_γ_τ_lift h_zero_mem h_agree_at_zero
  -- Hence back_path_rev 1 = γ_raw (τ 1) = γ_raw 1.
  have h_one_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have h_back_rev_one_eq : back_path_rev 1 = γ_raw 1 := by
    have h1 := h_back_rev_eqOn h_one_mem
    show back_path_rev 1 = γ_raw 1
    have h2 : γ_raw (tau 1) = γ_raw 1 := by rw [hτ_one]
    exact h1.trans h2
  -- Now the forward side: fwd_path.toPath.extend lifts β ∘ σ on Icc 0 1.
  let fwd_ext : ℝ → X := fwd_path.toPath.extend
  have h_fwd_ext_cont : Continuous fwd_ext := fwd_path.toPath.extend.continuous
  have h_fwd_ext_lift : ∀ t ∈ Icc (0 : ℝ) 1,
      f.toRiemannSphere (fwd_ext t) = β (sigma t) := by
    intro t ht
    show f.toRiemannSphere (fwd_path.toPath.extend t) = β (sigma t)
    rw [Path.extend_extends' fwd_path.toPath ⟨t, ht⟩]
    exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx_lift ⟨t, ht⟩
  -- γ_raw ∘ σ lifts β ∘ σ on Icc 0 1.
  have h_γ_σ_lift : ∀ t ∈ Icc (0 : ℝ) 1,
      f.toRiemannSphere (γ_raw (sigma t)) = β (sigma t) := by
    intro t _
    exact hγ_lift (sigma t) (hσ_range t)
  have h_γ_σ_cont : Continuous (fun t => γ_raw (sigma t)) :=
    hγ_cont.comp hσ_cont
  -- fwd_ext 0 = fwd_path.src = x.
  have h_fwd_ext_zero : fwd_ext 0 = x := by
    show fwd_path.toPath.extend 0 = x
    rw [Path.extend_zero, h_fwd_src]
  have h_fwd_agree_at_zero : fwd_ext 0 = γ_raw (sigma 0) := by
    rw [hσ_zero, hγ_zero, h_fwd_ext_zero]
  -- Apply path_lift_eqOn_Icc to β ∘ σ on Icc 0 1 at t₀ = 0.
  have h_fwd_eqOn :
      Set.EqOn fwd_ext (fun t => γ_raw (sigma t)) (Icc (0 : ℝ) 1) :=
    f.path_lift_eqOn_Icc hβσ_reg h_fwd_ext_cont h_γ_σ_cont
      h_fwd_ext_lift h_γ_σ_lift h_zero_mem h_fwd_agree_at_zero
  -- Hence fwd_ext 1 = γ_raw (σ 1) = γ_raw 1.
  have h_fwd_ext_one_eq : fwd_ext 1 = γ_raw 1 := by
    have h1 := h_fwd_eqOn h_one_mem
    show fwd_ext 1 = γ_raw 1
    have h2 : γ_raw (sigma 1) = γ_raw 1 := by rw [hσ_one]
    exact h1.trans h2
  -- fwd_ext 1 = fwd_path.toPath.extend 1 = fwd_path.tgt.
  have h_fwd_ext_one_tgt : fwd_ext 1 = fwd_path.tgt := Path.extend_one _
  -- Combine: fwd_path.tgt = γ_raw 1 = back_path_rev 1 = y.
  refine ⟨x, hx_lift, ?_⟩
  show fwd_path.tgt = y
  rw [← h_fwd_ext_one_tgt, h_fwd_ext_one_eq, ← h_back_rev_one_eq, h_back_rev_one]

end MeromorphicNonzero

end JacobianChallenge

end
