/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftExistsOnIcc
import JacobianChallenge.Manifold.MeromorphicNonzeroSmoothLocalLiftOn
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth upgrade of the global continuous path lift on `Icc 0 T`

Given the global continuous lift `γ` from `exists_continuous_lift_on_Icc`
of a `C^∞` path `β : ℝ → RiemannSphere` whose values on `Icc 0 T`
are all regular for `f`, the same `γ` is in fact `ContMDiffOn 𝓘(ℝ,ℝ)
𝓘(ℝ,ℂ) ∞` on `Icc 0 T`.

This is the **smoothness upgrade** of the path lift: from continuous
to `C^∞`. The argument is local: at every `t₀ ∈ Icc 0 T`, the smooth
local lift `δ` (chip 15, `exists_contMDiffOn_local_lift`) anchored at
`γ t₀` agrees with `γ` on a closed sub-interval inside the smooth
chart's open domain (by `path_lift_eqOn_Icc`). Smoothness within
`Icc 0 T` at `t₀` then transfers via
`ContMDiffWithinAt.congr_of_eventuallyEq_of_mem`.

## What ships

* `MeromorphicNonzero.contMDiffOn_lift_of_continuous_lift` — the
  smoothness-transfer theorem.
* `MeromorphicNonzero.exists_contMDiffOn_lift_on_Icc` — bundled
  headline: existence of a `ContMDiffOn ∞` lift on `Icc 0 T`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Smoothness transfer for the continuous lift.**

If `γ : ℝ → X` is a continuous lift of a `C^∞` path `β` whose values
on `Icc 0 T` are all regular for `f`, then `γ` is in fact `ContMDiffOn
𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞` on `Icc 0 T`. -/
theorem contMDiffOn_lift_of_continuous_lift
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    {γ : ℝ → X} (hγ_cont : Continuous γ)
    (hγ_lift : ∀ t ∈ Icc 0 T, f.toRiemannSphere (γ t) = β t) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ (Icc 0 T) := by
  classical
  intro t₀ ht₀
  -- Local smooth lift δ via chip 15 at t₀ with anchor γ t₀.
  have hβt₀_reg : β t₀ ∈ f.regularValueSet := hβ_reg t₀ ht₀
  have hγt₀_lift : f.toRiemannSphere (γ t₀) = β t₀ := hγ_lift t₀ ht₀
  obtain ⟨W, hW_open, ht₀_W, δ, hδ_smooth, hδ_zero, hδ_lift⟩ :=
    f.exists_contMDiffOn_local_lift hnc hβ_smooth hβt₀_reg hγt₀_lift
  -- ε > 0 with Metric.ball t₀ ε ⊆ W.
  rw [Metric.isOpen_iff] at hW_open
  obtain ⟨ε, hε_pos, hε_ball⟩ := hW_open t₀ ht₀_W
  -- Sub-interval J := Icc a b ⊆ W ∩ Icc 0 T, with t₀ ∈ J.
  let a : ℝ := max 0 (t₀ - ε / 2)
  let b : ℝ := min T (t₀ + ε / 2)
  have h_a_nonneg : 0 ≤ a := le_max_left _ _
  have h_a_ge_low : t₀ - ε / 2 ≤ a := le_max_right _ _
  have h_b_le_hi : b ≤ t₀ + ε / 2 := min_le_right _ _
  have h_a_le_t₀ : a ≤ t₀ :=
    max_le ht₀.1 (by linarith)
  have h_t₀_le_b : t₀ ≤ b :=
    le_min ht₀.2 (by linarith)
  have h_b_le_T : b ≤ T := min_le_left _ _
  have h_a_le_b : a ≤ b := le_trans h_a_le_t₀ h_t₀_le_b
  have h_t₀_mem_J : t₀ ∈ Icc a b := ⟨h_a_le_t₀, h_t₀_le_b⟩
  have h_J_sub_Icc : Icc a b ⊆ Icc 0 T := fun t ht =>
    ⟨h_a_nonneg.trans ht.1, ht.2.trans h_b_le_T⟩
  -- J ⊆ W via [t₀-ε/2, t₀+ε/2] ⊆ Metric.ball t₀ ε ⊆ W.
  have h_J_sub_W : Icc a b ⊆ W := by
    intro t ht
    have h_dist : dist t t₀ < ε := by
      rw [Real.dist_eq]
      have h_low : t₀ - ε / 2 ≤ t := h_a_ge_low.trans ht.1
      have h_hi : t ≤ t₀ + ε / 2 := ht.2.trans h_b_le_hi
      have h_abs : |t - t₀| ≤ ε / 2 := by
        rw [abs_le]; constructor <;> linarith
      linarith
    exact hε_ball h_dist
  -- β is regular on J (J ⊆ Icc 0 T).
  have hβ_reg_J : ∀ t ∈ Icc a b, β t ∈ f.regularValueSet :=
    fun t ht => hβ_reg t (h_J_sub_Icc ht)
  -- γ and δ both lift β on J (γ via hypothesis; δ via chip 15 + J ⊆ W).
  have hγ_lift_J : ∀ t ∈ Icc a b, f.toRiemannSphere (γ t) = β t :=
    fun t ht => hγ_lift t (h_J_sub_Icc ht)
  have hδ_lift_J : ∀ t ∈ Icc a b, f.toRiemannSphere (δ t) = β t :=
    fun t ht => hδ_lift t (h_J_sub_W ht)
  -- γ t₀ = δ t₀ via hδ_zero.
  have h_agree_t₀ : γ t₀ = δ t₀ := hδ_zero.symm
  -- δ is continuous (smooth → continuous on W; we need global continuity).
  -- Use ContMDiffOn.continuousOn + Continuous.continuousOn → ContMDiffWithinAt at t₀ via 𝓝[Icc a b].
  -- For path_lift_eqOn_Icc, we need Continuous of δ on all of ℝ; only have on W.
  -- Restrict the uniqueness argument to ContinuousOn on the closed interval [a, b] inside W.
  have hδ_contOn_W : ContinuousOn δ W := hδ_smooth.continuousOn
  have hδ_contOn_J : ContinuousOn δ (Icc a b) :=
    hδ_contOn_W.mono h_J_sub_W
  -- Glue δ on (Icc a b) to a globally continuous extension γ_δ.
  -- For path_lift_eqOn_Icc we want two globally continuous lifts. Construct
  -- δ_glob : ℝ → X agreeing with δ on (Icc a b) and γ outside.
  let δ_glob : ℝ → X := fun t =>
    if t < a then γ a else if t > b then γ b else δ t
  -- This is continuous: on Iio a, equals γ a (constant); on Ioi b, equals γ b (constant);
  -- on Icc a b, equals δ. We use path_lift_eqOn_Icc which works on the closed interval.
  -- Actually simpler: use the fact that δ agrees with γ on the *Icc*, and apply
  -- path_lift_eqOn_Icc on Icc a b with two continuous lifts γ and a globally-continuous
  -- extension of δ. The extension built via `if a ≤ t ∧ t ≤ b then δ t else γ t`.
  -- Or use δ_ext := piecewise interpolation. We need any global continuous extension δ̃ of δ|J
  -- to apply path_lift_eqOn_Icc.
  -- Simpler approach: clip the argument to [a, b]. Inside J, δ_glob t = δ t.
  let clip : ℝ → ℝ := fun t => max a (min b t)
  have h_clip_cont : Continuous clip :=
    (continuous_const.max (continuous_const.min continuous_id))
  have h_clip_in : ∀ t : ℝ, clip t ∈ Icc a b := fun t =>
    ⟨le_max_left _ _, max_le h_a_le_b (min_le_left _ _)⟩
  have h_clip_id : ∀ t ∈ Icc a b, clip t = t := fun t ht => by
    show max a (min b t) = t
    rw [min_eq_right ht.2, max_eq_right ht.1]
  let δ_clip : ℝ → X := fun t => δ (clip t)
  have hδ_clip_cont : Continuous δ_clip := by
    have h_mapsTo : ∀ t, clip t ∈ Icc a b := h_clip_in
    have h_cont_on_univ : ContinuousOn δ_clip Set.univ := by
      refine hδ_contOn_J.comp h_clip_cont.continuousOn ?_
      intro t _
      exact h_mapsTo t
    rwa [continuousOn_univ] at h_cont_on_univ
  -- δ_clip = δ on Icc a b.
  have hδ_clip_eq_δ : ∀ t ∈ Icc a b, δ_clip t = δ t := fun t ht => by
    show δ (clip t) = δ t
    rw [h_clip_id t ht]
  -- δ_clip lifts β on Icc a b.
  have hδ_clip_lift_J : ∀ t ∈ Icc a b, f.toRiemannSphere (δ_clip t) = β t := by
    intro t ht
    rw [hδ_clip_eq_δ t ht]
    exact hδ_lift_J t ht
  -- δ_clip t₀ = δ t₀ = γ t₀.
  have hδ_clip_at_t₀ : δ_clip t₀ = γ t₀ := by
    rw [hδ_clip_eq_δ t₀ h_t₀_mem_J, ← h_agree_t₀]
  -- Apply path_lift_eqOn_Icc to (γ, δ_clip) on Icc a b.
  have h_eqOn_J : Set.EqOn γ δ_clip (Icc a b) :=
    f.path_lift_eqOn_Icc hβ_reg_J hγ_cont hδ_clip_cont
      hγ_lift_J hδ_clip_lift_J h_t₀_mem_J hδ_clip_at_t₀.symm
  -- Hence γ = δ on Icc a b.
  have h_γ_eq_δ_on_J : ∀ t ∈ Icc a b, γ t = δ t := fun t ht => by
    have h1 : γ t = δ_clip t := h_eqOn_J ht
    rw [h1, hδ_clip_eq_δ t ht]
  -- Icc a b is in 𝓝[Icc 0 T] t₀: take open U = Ioo (t₀ - ε/2 - 1) (t₀ + ε/2 + 1) ∋ t₀
  --   intersected with Icc 0 T ⊆ Icc a b? Need careful nbhd-within argument.
  -- Standard route: show Icc a b ∈ 𝓝[Icc 0 T] t₀.
  have h_J_nhdsWithin : Icc a b ∈ 𝓝[Icc 0 T] t₀ := by
    -- Find open U ⊆ ℝ with t₀ ∈ U and U ∩ Icc 0 T ⊆ Icc a b.
    -- Take U := Ioo (t₀ - ε/2) (t₀ + ε/2) intersected appropriately.
    -- Actually simpler: take U := Ioo (t₀ - ε/2 - 1) (t₀ + ε/2 + 1) ... no that's too big.
    -- The right U: any open interval centered at t₀ with radius < ε/2 + extras.
    -- Key insight: a = max 0 (t₀ - ε/2); b = min T (t₀ + ε/2).
    -- For t ∈ Icc 0 T with |t - t₀| < ε/2: t > t₀ - ε/2 and t < t₀ + ε/2.
    -- Then t ≥ t - 0 ≥ 0 (since t ∈ Icc 0 T), so t > t₀ - ε/2 and t ≥ 0 ⇒ t ≥ a.
    --      Similarly t ≤ T and t < t₀ + ε/2 ⇒ t ≤ b. Done.
    refine mem_nhdsWithin.mpr ⟨Ioo (t₀ - ε / 2) (t₀ + ε / 2), isOpen_Ioo, ?_, ?_⟩
    · constructor <;> linarith
    · intro t ht
      have h_t_in_Icc : t ∈ Icc 0 T := ht.2
      have h_t_lo : t₀ - ε / 2 < t := ht.1.1
      have h_t_hi : t < t₀ + ε / 2 := ht.1.2
      refine ⟨max_le h_t_in_Icc.1 (by linarith), le_min h_t_in_Icc.2 (by linarith)⟩
  -- γ =ᶠ[𝓝[Icc 0 T] t₀] δ.
  have h_eq_eventually : γ =ᶠ[𝓝[Icc 0 T] t₀] δ := by
    filter_upwards [h_J_nhdsWithin] with t ht using h_γ_eq_δ_on_J t ht
  -- ContMDiffWithinAt δ (Icc 0 T) t₀ via W ∈ 𝓝 t₀ + ContMDiffOn.contMDiffAt + .contMDiffWithinAt.
  have hW_nhds_t₀ : W ∈ 𝓝 t₀ := by
    rw [Metric.mem_nhds_iff]
    exact ⟨ε, hε_pos, hε_ball⟩
  have hδ_contMDiffAt_t₀ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ δ t₀ :=
    hδ_smooth.contMDiffAt hW_nhds_t₀
  have hδ_contMDiffWithinAt :
      ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ δ (Icc 0 T) t₀ :=
    hδ_contMDiffAt_t₀.contMDiffWithinAt
  -- Transfer via congr_of_eventuallyEq_of_mem.
  exact hδ_contMDiffWithinAt.congr_of_eventuallyEq_of_mem h_eq_eventually ht₀

/-- **Bundled existence: continuous + smooth global lift on `Icc 0 T`.** -/
theorem exists_contMDiffOn_lift_on_Icc
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β) (x₀ : X)
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    (hx₀ : f.toRiemannSphere x₀ = β 0) (hT : 0 ≤ T) :
    ∃ γ : ℝ → X, Continuous γ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ (Icc 0 T) ∧
      γ 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, f.toRiemannSphere (γ t) = β t := by
  obtain ⟨γ, hγ_cont, hγ_zero, hγ_lift⟩ :=
    f.exists_continuous_lift_on_Icc hnc hβ_smooth.continuous x₀ hβ_reg hx₀ hT
  refine ⟨γ, hγ_cont, ?_, hγ_zero, hγ_lift⟩
  exact f.contMDiffOn_lift_of_continuous_lift hnc hβ_smooth hβ_reg hγ_cont hγ_lift

end MeromorphicNonzero

end JacobianChallenge

end
