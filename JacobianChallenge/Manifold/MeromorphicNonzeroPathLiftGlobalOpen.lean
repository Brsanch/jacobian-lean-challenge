/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftGlobal
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftAtPoint
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Openness of `liftReachable` (clean version via clip+if_le)

`liftReachable_extends_right`: if `b ∈ f.liftReachable β x₀ T` with
`b < T`, there is `ε > 0` (with `b + ε ≤ T`) and `b + ε ∈
f.liftReachable β x₀ T`.

The globally-continuous lift `γ_glob` is built via clip-and-if_le:

  `γ_glob t := if t ≤ b then γ t else sheet.g (β (clip t))`

where `clip t := max b (min (b + ε) t)` projects `t` onto `[b, b + ε]`.
Both `γ` and `sheet.g ∘ β ∘ clip` are continuous on ℝ (the clip keeps
β inside `sheet.V` everywhere), and they agree at `b`.  `Continuous.if_le`
delivers global continuity.

## What ships

* `MeromorphicNonzero.liftReachable_extends_right` — openness.

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

/-- **Openness extension** of `liftReachable`. -/
theorem liftReachable_extends_right
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β) {x₀ : X}
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    {b : ℝ} (hb_mem : b ∈ f.liftReachable β x₀ T)
    (hb_lt : b < T) :
    ∃ ε > (0 : ℝ), b + ε ≤ T ∧ b + ε ∈ f.liftReachable β x₀ T := by
  classical
  obtain ⟨hb_in_Icc, γ, hγ_cont, hγ_0, hγ_lift⟩ := hb_mem
  have hγb_lift : f.toRiemannSphere (γ b) = β b :=
    hγ_lift b ⟨hb_in_Icc.1, le_refl b⟩
  have hβb_reg : β b ∈ f.regularValueSet := hβ_reg b hb_in_Icc
  obtain ⟨hγb_reg, ε₀, hε₀_pos, hγb_U, hβ_in_V⟩ :=
    f.exists_sheet_data_extending_to_right hnc hβ_cont hβb_reg hγb_lift
  -- Shrink ε so that b + ε ≤ T.
  set ε : ℝ := min ε₀ (T - b) with hε_def
  have hε_pos : 0 < ε := lt_min hε₀_pos (by linarith)
  have hε_le_T : b + ε ≤ T := by
    have : ε ≤ T - b := min_le_right _ _; linarith
  have hε_le_ε₀ : ε ≤ ε₀ := min_le_left _ _
  set sheet := f.localSheetData_at_regular hnc hγb_reg with hsheet_def
  -- β maps Icc b (b + ε) into sheet.V.
  have hβ_in_V' : ∀ t ∈ Icc b (b + ε), β t ∈ sheet.V := by
    intro t ht
    exact hβ_in_V t ⟨ht.1, ht.2.trans (by linarith)⟩
  -- Clipping function: clip t = max b (min (b + ε) t) ∈ [b, b + ε] always.
  let clip : ℝ → ℝ := fun t => max b (min (b + ε) t)
  have h_clip_cont : Continuous clip :=
    (continuous_const.max (continuous_const.min continuous_id))
  have h_clip_in : ∀ t : ℝ, clip t ∈ Icc b (b + ε) := by
    intro t
    refine ⟨le_max_left _ _, ?_⟩
    refine max_le (by linarith) ?_
    exact min_le_left _ _
  have h_clip_id : ∀ t ∈ Icc b (b + ε), clip t = t := by
    intro t ht
    show max b (min (b + ε) t) = t
    have : min (b + ε) t = t := min_eq_right ht.2
    rw [this, max_eq_right ht.1]
  -- h t := sheet.g (β (clip t)): continuous globally.
  let h : ℝ → X := fun t => sheet.g (β (clip t))
  have h_cont : Continuous h := by
    have hβ_clip_cont : Continuous (fun t => β (clip t)) :=
      hβ_cont.comp h_clip_cont
    have h_g_cont_on : ContinuousOn sheet.g sheet.V := sheet.g_continuousOn
    have h_mapsTo : ∀ t : ℝ, β (clip t) ∈ sheet.V := fun t =>
      hβ_in_V' (clip t) (h_clip_in t)
    -- Continuous via ContinuousOn.comp_continuous on global function.
    have h_cont_on_univ : ContinuousOn h Set.univ := by
      refine h_g_cont_on.comp hβ_clip_cont.continuousOn ?_
      intro t _
      exact h_mapsTo t
    rwa [continuousOn_univ] at h_cont_on_univ
  -- Agreement at b: γ b = h b.
  have h_agree_at_b : γ b = h b := by
    show γ b = sheet.g (β (clip b))
    rw [h_clip_id b ⟨le_refl _, by linarith⟩]
    -- h b = sheet.g (β b) = sheet.g (f.toRS γ b) = γ b
    have h_inv : sheet.g (f.toRiemannSphere (γ b)) = γ b :=
      sheet.leftInvOn hγb_U
    -- sheet.g (β b) = sheet.g (f.toRS (γ b)) = γ b, via hγb_lift.
    have h_β_eq_fγ : β b = f.toRiemannSphere (γ b) := hγb_lift.symm
    show γ b = sheet.g (β b)
    rw [h_β_eq_fγ, h_inv]
  -- γ_glob: piecewise continuous global lift.
  let γ_glob : ℝ → X := fun t => if t ≤ b then γ t else h t
  have hγ_glob_cont : Continuous γ_glob := by
    refine Continuous.if_le hγ_cont h_cont continuous_id continuous_const ?_
    intro t ht
    rw [ht]; exact h_agree_at_b
  -- Package.
  refine ⟨ε, hε_pos, hε_le_T, ?_, γ_glob, hγ_glob_cont, ?_, ?_⟩
  · refine ⟨?_, hε_le_T⟩
    have : (0 : ℝ) ≤ b := hb_in_Icc.1; linarith
  · -- γ_glob 0 = x₀.
    show (if (0 : ℝ) ≤ b then γ 0 else h 0) = x₀
    rw [if_pos hb_in_Icc.1, hγ_0]
  · -- Lift on Icc 0 (b + ε).
    intro t ht
    show f.toRiemannSphere (if t ≤ b then γ t else h t) = β t
    by_cases htb : t ≤ b
    · rw [if_pos htb]
      exact hγ_lift t ⟨ht.1, htb⟩
    · push Not at htb
      rw [if_neg (not_le.mpr htb)]
      show f.toRiemannSphere (sheet.g (β (clip t))) = β t
      have ht_in : t ∈ Icc b (b + ε) := ⟨le_of_lt htb, ht.2⟩
      rw [h_clip_id t ht_in]
      exact sheet.rightInvOn (hβ_in_V' t ht_in)

end MeromorphicNonzero

end JacobianChallenge

end
