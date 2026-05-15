/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftExtend

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Local extension of a continuous path lift at a regular-value point

At any point `z ∈ X` lying over a regular value `β a ∈ f.regularValueSet`,
the `LocalSheetData` at `z` provides:
* `z ∈ sheet.U` (chip 7's `mem_source_manifoldLocalOph`),
* `β a ∈ sheet.V` (chip 7's `mem_target_manifoldLocalOph` at the
   appropriate base value),
* an open nbhd `[a, a+ε]` with `β` mapping into `sheet.V` (continuity).

Combined with `extend_lift_across_sheet` (chip 19), this lets us
extend any continuous partial lift past `a` by a positive amount.

## What ships

* `MeromorphicNonzero.exists_sheet_data_extending_to_right` — the
  local extension data at a lift point.
* `MeromorphicNonzero.extend_continuous_lift_to_right` — the
  corresponding extension theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Local sheet at a lift point extends `β` past `a`.**

For `z ∈ X` over `β a ∈ regularValueSet`, the local sheet at `z` has
`z ∈ U`, `β a ∈ V`, and (by continuity of `β`) `β` maps `[a, a + ε]`
into `V` for some `ε > 0`. -/
theorem exists_sheet_data_extending_to_right
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    {z : X} {a : ℝ}
    (hβa_reg : β a ∈ f.regularValueSet)
    (hz_lift : f.toRiemannSphere z = β a) :
    ∃ (hz_reg : z ∈ f.regularSet) (ε : ℝ), 0 < ε ∧
      z ∈ (f.localSheetData_at_regular hnc hz_reg).U ∧
      ∀ t ∈ Icc a (a + ε), β t ∈
        (f.localSheetData_at_regular hnc hz_reg).V := by
  classical
  have hz_reg : z ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hβa_reg hz_lift
  -- z ∈ sheet.U.
  have hz_U : z ∈ (f.localSheetData_at_regular hnc hz_reg).U :=
    (f.localSheetData_at_regular hnc hz_reg).mem_U
  -- β a ∈ sheet.V.
  have hβa_V : β a ∈ (f.localSheetData_at_regular hnc hz_reg).V := by
    have h : f.toRiemannSphere z ∈ (f.localSheetData_at_regular hnc hz_reg).V :=
      (f.localSheetData_at_regular hnc hz_reg).mem_V
    exact hz_lift ▸ h
  -- β⁻¹' sheet.V is open in ℝ and contains a.
  have hpre_open : IsOpen (β ⁻¹' (f.localSheetData_at_regular hnc hz_reg).V) :=
    (f.localSheetData_at_regular hnc hz_reg).V_open.preimage hβ_cont
  have ha_pre : a ∈ β ⁻¹' (f.localSheetData_at_regular hnc hz_reg).V := hβa_V
  -- An open nbhd of a is contained in β⁻¹ sheet.V; extract ε > 0 with
  -- Icc a (a + ε) ⊆ β⁻¹ sheet.V.
  rw [Metric.isOpen_iff] at hpre_open
  obtain ⟨ε, hε_pos, hε_ball⟩ := hpre_open a ha_pre
  refine ⟨hz_reg, ε / 2, by linarith, hz_U, ?_⟩
  intro t ht
  -- t ∈ Icc a (a + ε/2): show |t - a| < ε.
  have h_dist : |t - a| < ε := by
    have ht1 : a ≤ t := ht.1
    have ht2 : t ≤ a + ε / 2 := ht.2
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - a)]
    linarith
  have ht_in_ball : t ∈ Metric.ball a ε := by
    show dist t a < ε
    rwa [Real.dist_eq]
  exact hε_ball ht_in_ball

/-- **Extension of a continuous path lift to the right.**

Given a continuous lift `γ` of `β` on `Icc a b` with `γ b = z`, and
`β b ∈ regularValueSet`, the lift extends to `Icc a (b + ε)` for some
`ε > 0` via the local sheet at `z`. -/
theorem extend_continuous_lift_to_right
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    {γ : ℝ → X} (hγ_cont : Continuous γ)
    {a b : ℝ} (hab : a ≤ b)
    (hγ_lift : ∀ t ∈ Icc a b, f.toRiemannSphere (γ t) = β t)
    (hβb_reg : β b ∈ f.regularValueSet) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ' : ℝ → X,
      ContinuousOn γ' (Icc a (b + ε)) ∧
      (∀ t ∈ Iic b, γ' t = γ t) ∧
      (∀ t ∈ Icc a (b + ε), f.toRiemannSphere (γ' t) = β t) := by
  classical
  -- γ b lifts β b.
  have hγb_lift : f.toRiemannSphere (γ b) = β b :=
    hγ_lift b ⟨hab, le_refl b⟩
  -- Local sheet data extending β past b.
  obtain ⟨hγb_reg, ε, hε_pos, hγb_U, hβ_in_V⟩ :=
    f.exists_sheet_data_extending_to_right hnc hβ_cont hβb_reg hγb_lift
  refine ⟨ε, hε_pos, ?_⟩
  -- Apply chip 19's extension lemma with c := b + ε.
  obtain ⟨γ', hγ'_cont_on, hγ'_le_b, hγ'_lift⟩ :=
    f.extend_lift_across_sheet hnc hβ_cont hγ_cont hab
      (by linarith : b ≤ b + ε) hγ_lift hγb_reg hβ_in_V hγb_U
  exact ⟨γ', hγ'_cont_on, hγ'_le_b, hγ'_lift⟩

end MeromorphicNonzero

end JacobianChallenge

end
