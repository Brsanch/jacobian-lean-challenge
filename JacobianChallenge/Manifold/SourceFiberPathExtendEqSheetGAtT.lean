/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOnContinuousOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Local identification of `(sourceFiberPath p).extend` with sheet at lifted point

The existing chip `sourceFiberPath_toPath_extend_eq_sheet_g_locally`
identifies `(sourceFiberPath p).toPath.extend t = sheet_x.g (β(σ t))`
on a sub-interval `[0, δ]`, where `sheet_x` is centered at the
**source fibre point `p`** (over `β 0`).

This file provides the analog at any `t₀ ∈ Icc 0 1`: identify
`(sourceFiberPath p).toPath.extend t = sheet_q.g (β(σ t))` on a
sub-interval around `t₀`, where `q := (sourceFiberPath p).toPath.extend t₀`
is the **lifted point** at time `t₀` (in the fibre over `β(σ t₀)`).

The lifted-point sheet `sheet_q` is centered at `q`, so
`sheet_q.V` is a nbhd of `f.toRiemannSphere q = β(σ t₀)`. By
continuity of `β ∘ σ`, an interval around `t₀` is mapped into
`sheet_q.V`. On this interval, both the `Path.extend` and the explicit
`sheet_q.g ∘ β ∘ σ` lift `β ∘ σ` and agree at `t₀` (= q). By
`path_lift_eqOn_Icc_of_continuousOn`, they agree on the interval.

This is the **lifted-point chain rule's foundational lemma**: at any
`t₀ ∈ [0, 1]`, the path's extension is locally given by sheet evaluation
at the lifted point. The lifted-point sheet always satisfies the
sub-interval condition `β(σ t) ∈ sheet_q.V` (in a nbhd of `t₀`), so
the chain rule based at sheet_q works at every `t₀` — bypassing the
β 0-centered sub-interval restriction of the original chain rule.

## What ships

* `MeromorphicNonzero.sourceFiberPath_toPath_extend_eq_sheet_g_locally_at` —
  local identification at general `t₀`.

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

/-- **Local identification at general `t₀`.**

For `t₀ ∈ Icc 0 1` and the lifted point
`q := (sourceFiberPath p).toPath.extend t₀`, there exist `a, b ∈ [0, 1]`
with `a ≤ t₀ ≤ b` such that on `[a, b]`,
`(sourceFiberPath p).toPath.extend t = sheet_q.g (β(σ t))`. -/
theorem sourceFiberPath_toPath_extend_eq_sheet_g_locally_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    let γ := (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend
    let q := γ t₀
    let hβσt₀_reg : β (Real.smoothTransition t₀) ∈ f.regularValueSet :=
      hβ_reg (Real.smoothTransition t₀)
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    let hq_lift : f.toRiemannSphere q = β (Real.smoothTransition t₀) := by
      show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t₀)
        = β (Real.smoothTransition t₀)
      rw [Path.extend_extends'
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨t₀, ht₀⟩]
      exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx ⟨t₀, ht₀⟩
    let hq_reg : q ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hβσt₀_reg hq_lift
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≤ t₀ ∧ t₀ ≤ b ∧
      (0 < t₀ → a < t₀) ∧ (t₀ < 1 → t₀ < b) ∧
      ∀ t ∈ Icc a b,
        γ t = (f.localSheetData_at_regular hnc hq_reg).g
          (β (Real.smoothTransition t)) := by
  classical
  intro γ q hβσt₀_reg hq_lift hq_reg
  set sheet := f.localSheetData_at_regular hnc hq_reg with hsheet_def
  -- β(σ t₀) ∈ sheet.V (nbhd of f.toRiemannSphere q = β(σ t₀)).
  have hβσt₀_in_V : β (Real.smoothTransition t₀) ∈ sheet.V := by
    have h_mem : f.toRiemannSphere q ∈ sheet.V := sheet.mem_V
    exact Eq.subst (motive := fun w => w ∈ sheet.V) hq_lift h_mem
  -- q ∈ sheet.U.
  have hq_in_U : q ∈ sheet.U := sheet.mem_U
  -- γ continuous globally (Path.extend).
  have hγ_cont : Continuous γ :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.continuous_extend
  -- β ∘ σ continuous.
  have hβσ_cont : Continuous (fun t : ℝ => β (Real.smoothTransition t)) :=
    hβ_smooth.continuous.comp Real.smoothTransition.continuous
  -- (β ∘ σ) ⁻¹' sheet.V is open.
  have hpre_V_open : IsOpen ((fun t : ℝ => β (Real.smoothTransition t))
      ⁻¹' sheet.V) :=
    hβσ_cont.isOpen_preimage _ sheet.V_open
  -- t₀ ∈ (β ∘ σ) ⁻¹' sheet.V.
  have ht₀_in_pre_V : t₀ ∈ (fun t : ℝ => β (Real.smoothTransition t)) ⁻¹' sheet.V :=
    hβσt₀_in_V
  -- γ ⁻¹' sheet.U is open.
  have hpre_U_open : IsOpen (γ ⁻¹' sheet.U) :=
    hγ_cont.isOpen_preimage _ sheet.U_open
  -- t₀ ∈ γ ⁻¹' sheet.U.
  have ht₀_in_pre_U : t₀ ∈ γ ⁻¹' sheet.U := hq_in_U
  -- Both preimages are nbhds of t₀.
  have hpre_V_nhds : (fun t : ℝ => β (Real.smoothTransition t)) ⁻¹' sheet.V ∈ 𝓝 t₀ :=
    hpre_V_open.mem_nhds ht₀_in_pre_V
  have hpre_U_nhds : γ ⁻¹' sheet.U ∈ 𝓝 t₀ :=
    hpre_U_open.mem_nhds ht₀_in_pre_U
  -- Intersect with [0, 1]: there's an ε-ball around t₀ in both preimages.
  obtain ⟨ε₁, hε₁_pos, hε₁_sub⟩ := Metric.mem_nhds_iff.mp hpre_V_nhds
  obtain ⟨ε₂, hε₂_pos, hε₂_sub⟩ := Metric.mem_nhds_iff.mp hpre_U_nhds
  set ε : ℝ := min ε₁ ε₂ with hε_def
  have hε_pos : 0 < ε := lt_min hε₁_pos hε₂_pos
  -- Define a := max 0 (t₀ - ε/2), b := min 1 (t₀ + ε/2).
  set a : ℝ := max 0 (t₀ - ε / 2) with ha_def
  set b : ℝ := min 1 (t₀ + ε / 2) with hb_def
  have ha_nonneg : 0 ≤ a := le_max_left _ _
  have ha_le_one : a ≤ 1 := by
    refine max_le (by norm_num) ?_
    have h1 : t₀ - ε / 2 ≤ t₀ := by linarith
    exact le_trans h1 ht₀.2
  have ha_le_t₀ : a ≤ t₀ := by
    refine max_le ht₀.1 ?_
    linarith
  have hb_nonneg : 0 ≤ b := by
    refine le_min (by norm_num) ?_
    have h_t₀ : (0 : ℝ) ≤ t₀ := ht₀.1
    have h_ε : 0 ≤ ε / 2 := by linarith
    linarith
  have hb_le_one : b ≤ 1 := min_le_left _ _
  have ht₀_le_b : t₀ ≤ b := by
    refine le_min ht₀.2 ?_
    linarith
  -- Strict bounds when t₀ ∈ Ioo 0 1.
  have ha_lt_t₀ : 0 < t₀ → a < t₀ := by
    intro ht₀_pos
    -- a = max 0 (t₀ - ε/2). For t₀ - ε/2 ≥ 0, a = t₀ - ε/2 < t₀.
    -- For t₀ - ε/2 < 0, a = 0 < t₀.
    rcases le_or_gt 0 (t₀ - ε / 2) with h | h
    · rw [show a = max 0 (t₀ - ε / 2) from rfl, max_eq_right h]
      linarith
    · rw [show a = max 0 (t₀ - ε / 2) from rfl, max_eq_left h.le]
      exact ht₀_pos
  have ht₀_lt_b : t₀ < 1 → t₀ < b := by
    intro ht₀_lt_one
    rcases le_or_gt (t₀ + ε / 2) 1 with h | h
    · rw [show b = min 1 (t₀ + ε / 2) from rfl, min_eq_right h]
      linarith
    · rw [show b = min 1 (t₀ + ε / 2) from rfl, min_eq_left h.le]
      exact ht₀_lt_one
  refine ⟨a, b, ⟨ha_nonneg, ha_le_one⟩, ⟨hb_nonneg, hb_le_one⟩,
    ha_le_t₀, ht₀_le_b, ha_lt_t₀, ht₀_lt_b, ?_⟩
  -- On [a, b], β(σ t) ∈ sheet.V and γ t ∈ sheet.U.
  have h_Iab_sub_ε : Icc a b ⊆ Metric.ball t₀ ε := by
    intro t ⟨hat, htb⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have : t₀ - ε / 2 ≤ t := le_trans (le_max_right _ _) hat
      linarith [hε_pos]
    · have : t ≤ t₀ + ε / 2 := le_trans htb (min_le_right _ _)
      linarith [hε_pos]
  have hβσ_mapsTo : Set.MapsTo (fun t : ℝ => β (Real.smoothTransition t))
      (Icc a b) sheet.V := by
    intro t ht
    apply hε₁_sub
    have h_t_in_ε : t ∈ Metric.ball t₀ ε := h_Iab_sub_ε ht
    rw [Metric.mem_ball] at h_t_in_ε ⊢
    exact lt_of_lt_of_le h_t_in_ε (min_le_left _ _)
  have hγ_mapsTo : Set.MapsTo γ (Icc a b) sheet.U := by
    intro t ht
    apply hε₂_sub
    have h_t_in_ε : t ∈ Metric.ball t₀ ε := h_Iab_sub_ε ht
    rw [Metric.mem_ball] at h_t_in_ε ⊢
    exact lt_of_lt_of_le h_t_in_ε (min_le_right _ _)
  -- γ₂ := sheet.g ∘ β ∘ σ.
  set γ₂ : ℝ → X := fun t => sheet.g (β (Real.smoothTransition t)) with hγ₂_def
  have hγ₂_contOn : ContinuousOn γ₂ (Icc a b) :=
    sheet.g_continuousOn.comp' hβσ_cont.continuousOn hβσ_mapsTo
  -- Both lift β ∘ σ on [a, b].
  have hγ_lift : ∀ t ∈ Icc a b,
      f.toRiemannSphere (γ t) = β (Real.smoothTransition t) := by
    intro t ht
    have ht_unit : t ∈ unitInterval :=
      ⟨le_trans ha_nonneg ht.1, le_trans ht.2 hb_le_one⟩
    show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t)
          = β (Real.smoothTransition t)
    rw [Path.extend_extends' _ ⟨t, ht_unit⟩]
    exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx ⟨t, ht_unit⟩
  have hγ₂_lift : ∀ t ∈ Icc a b,
      f.toRiemannSphere (γ₂ t) = β (Real.smoothTransition t) := by
    intro t ht
    show f.toRiemannSphere (sheet.g (β (Real.smoothTransition t)))
      = β (Real.smoothTransition t)
    exact sheet.rightInvOn (hβσ_mapsTo ht)
  -- β ∘ σ regular on [a, b].
  have hβσ_reg : ∀ t ∈ Icc a b,
      β (Real.smoothTransition t) ∈ f.regularValueSet := by
    intro t _
    exact hβ_reg (Real.smoothTransition t)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- Agreement at t₀: γ t₀ = q = sheet.g (β(σ t₀)).
  have h_agree_at_t₀ : γ t₀ = γ₂ t₀ := by
    show q = sheet.g (β (Real.smoothTransition t₀))
    -- sheet.g(β(σ t₀)) = sheet.g(f.toRiemannSphere q) = q (leftInvOn at q ∈ sheet.U).
    rw [show β (Real.smoothTransition t₀) = f.toRiemannSphere q from hq_lift.symm]
    exact (sheet.leftInvOn hq_in_U).symm
  -- Apply uniqueness.
  have h_eqOn : Set.EqOn γ γ₂ (Icc a b) :=
    f.path_lift_eqOn_Icc_of_continuousOn hβσ_reg hγ_cont.continuousOn
      hγ₂_contOn hγ_lift hγ₂_lift ⟨ha_le_t₀, ht₀_le_b⟩ h_agree_at_t₀
  intro t ht
  exact h_eqOn ht

end MeromorphicNonzero

end JacobianChallenge

end
