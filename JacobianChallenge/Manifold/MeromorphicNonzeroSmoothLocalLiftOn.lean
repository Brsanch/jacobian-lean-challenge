/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmoothOn
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalPathLift
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.ContMDiffRealification

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth local path lift on an open neighbourhood

Combines the open-nbhd smoothness of the local sheet inverse (chip 14)
with realification (`ContMDiffAt.complex_to_real`) and a ContMDiffAt
composition argument at every point to produce a `ContMDiffOn 𝓘(ℝ,ℝ)
𝓘(ℝ,ℂ) ∞` smooth local lift.

## What ships

* `MeromorphicNonzero.exists_contMDiffOn_local_lift` — for a globally
  `ContMDiff` path β with `β t₀ ∈ f.regularValueSet`, produces an open
  neighbourhood `W ⊆ ℝ` of `t₀` and a smooth (`ContMDiffOn 𝓘(ℝ,ℝ)
  𝓘(ℝ,ℂ) ∞`) lift `γ : ℝ → X` with `γ t₀ = x₀` and `f.toRiemannSphere
  ∘ γ = β` on `W`.

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

/-- **Smooth local path lift on an open neighbourhood of `t₀`.**

The lift `γ = (f.localSheetData_at_regular hnc hx₀_reg).g ∘ β` is `ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞` on the
open set `W := β ⁻¹' ((f.localSheetData_at_regular hnc hx₀_reg).V ∩ u)` where `u` is the open neighbourhood
of `v₀` from chip 14.  Pointwise: for `t ∈ W`, ContMDiffAt of γ at t
comes from chip 12 + `ContMDiffAt.complex_to_real` + composition. -/
theorem exists_contMDiffOn_local_lift
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    {t₀ : ℝ}
    (hvreg : β t₀ ∈ f.regularValueSet)
    {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β t₀) :
    ∃ W : Set ℝ, IsOpen W ∧ t₀ ∈ W ∧
      ∃ γ : ℝ → X,
        ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ W ∧
        γ t₀ = x₀ ∧
        ∀ t ∈ W, f.toRiemannSphere (γ t) = β t := by
  classical
  have hx₀_reg : x₀ ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hvreg hx₀
  let sheet := f.localSheetData_at_regular hnc hx₀_reg
  set v₀ : RiemannSphere := f.toRiemannSphere x₀
  -- Open nbhd `u ∋ v₀` with `ContMDiffOn ω (f.localSheetData_at_regular hnc hx₀_reg).g u`.
  obtain ⟨u, hu_nhds, hu_smooth⟩ :=
    f.exists_contMDiffOn_localSheet_g_near_basePoint hnc hx₀_reg
  -- `u` is a nbhd of v₀; shrink to an open subset `u_o ⊆ u` with `v₀ ∈ u_o`.
  obtain ⟨u_o, hu_o_sub, hu_o_open, hv₀_u_o⟩ := mem_nhds_iff.mp hu_nhds
  -- Sheet.V ∋ v₀.
  have hv₀_V : v₀ ∈ (f.localSheetData_at_regular hnc hx₀_reg).V := (f.localSheetData_at_regular hnc hx₀_reg).mem_V
  set W : Set ℝ := β ⁻¹' ((f.localSheetData_at_regular hnc hx₀_reg).V ∩ u_o) with hW_def
  have hf_β_cont : Continuous β := hβ.continuous
  have hSheetV_u_o_open : IsOpen ((f.localSheetData_at_regular hnc hx₀_reg).V ∩ u_o) := (f.localSheetData_at_regular hnc hx₀_reg).V_open.inter hu_o_open
  have hW_open : IsOpen W := hSheetV_u_o_open.preimage hf_β_cont
  -- β t₀ = v₀ ∈ (f.localSheetData_at_regular hnc hx₀_reg).V ∩ u_o.
  have ht₀_W : t₀ ∈ W := by
    show β t₀ ∈ (f.localSheetData_at_regular hnc hx₀_reg).V ∩ u_o
    rw [hx₀.symm]
    exact ⟨hv₀_V, hv₀_u_o⟩
  refine ⟨W, hW_open, ht₀_W, (f.localSheetData_at_regular hnc hx₀_reg).g ∘ β, ?_, ?_, ?_⟩
  · -- ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ ((f.localSheetData_at_regular hnc hx₀_reg).g ∘ β) W.
    -- At every t ∈ W:
    --   • β t ∈ u_o ⊆ u and β t ∈ (f.localSheetData_at_regular hnc hx₀_reg).V.
    --   • ContMDiffAt 𝓘(ℂ,ℂ) ω (f.localSheetData_at_regular hnc hx₀_reg).g (β t) by hu_smooth (ContMDiffOn ω
    --     ⇒ ContMDiffAt at points of an open subset).
    --   • Realify to ContMDiffAt 𝓘(ℝ,ℂ) ∞ via complex_to_real.
    --   • Compose with ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ β t (from hβ).
    intro t htW
    have hβt_V : β t ∈ (f.localSheetData_at_regular hnc hx₀_reg).V := htW.1
    have hβt_u_o : β t ∈ u_o := htW.2
    have hβt_u : β t ∈ u := hu_o_sub hβt_u_o
    -- ContMDiffAt 𝓘(ℂ,ℂ) ω (f.localSheetData_at_regular hnc hx₀_reg).g (β t).
    have h_sheet_g_omega : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (f.localSheetData_at_regular hnc hx₀_reg).g (β t) :=
      hu_smooth.contMDiffAt (mem_of_superset (hu_o_open.mem_nhds hβt_u_o) hu_o_sub)
    -- Realify.
    have h_sheet_g_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f.localSheetData_at_regular hnc hx₀_reg).g (β t) :=
      ContMDiffAt.complex_to_real h_sheet_g_omega
    -- ContMDiffAt β t.
    have hβ_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β t := hβ t
    -- Compose.
    have h_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ ((f.localSheetData_at_regular hnc hx₀_reg).g ∘ β) t :=
      h_sheet_g_real.comp t hβ_at
    -- ContMDiffAt → ContMDiffWithinAt W t.
    exact h_at.contMDiffWithinAt
  · -- γ t₀ = x₀.
    show ((f.localSheetData_at_regular hnc hx₀_reg).g ∘ β) t₀ = x₀
    rw [Function.comp_apply, ← hx₀]
    exact (f.localSheetData_at_regular hnc hx₀_reg).leftInvOn (f.localSheetData_at_regular hnc hx₀_reg).mem_U
  · -- f.toRiemannSphere ∘ γ = β on W.
    intro t htW
    show f.toRiemannSphere ((f.localSheetData_at_regular hnc hx₀_reg).g (β t)) = β t
    exact (f.localSheetData_at_regular hnc hx₀_reg).rightInvOn htW.1

end MeromorphicNonzero

end JacobianChallenge

end
