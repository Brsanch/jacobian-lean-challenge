/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathExtendEqSheetGAtT
import JacobianChallenge.Manifold.SmoothPathVelocityFromFun

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-fibre integrand at general `t₀` via lifted-point sheet

For `t₀ ∈ Icc 0 1`, the per-fibre integrand
`(sourceFiberPath p).integrand om u` at any `u` in the sub-interval
`(a, b)` of the local-identification chip's interval `[a, b]` equals
`applyCotangent (ω(sheet_q.g(β(σ u)))) (mfderiv (sheet_q.g ∘ β ∘ σ) u 1)`,
where `q := (sourceFiberPath p).toPath.extend t₀` is the lifted point.

This composes:
* `sourceFiberPath_toPath_extend_eq_sheet_g_locally_at` — local
  identification at general `t₀` (just landed).
* `integrand_eq_of_ambient_eqOn_Icc_fun` — integrand equality from
  ambient equality on a closed interval.

The RHS is the integrand of the path `sheet_q.g ∘ β ∘ σ` (which
locally agrees with the original lifted path). The chain rule's
unfolding into `cotangentPullbackAt sheet_q.g` form is layered on
top in subsequent chips.

## What ships

* `MeromorphicNonzero.sourceFiberPath_integrand_eq_local_at_lifted_sheet`
  — per-fibre integrand identity at general `t₀` via the lifted-point
  sheet.

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

/-- **Per-fibre integrand at general `t₀` via the lifted-point sheet.**

For `t₀ ∈ Icc 0 1` and the lifted point
`q := (sourceFiberPath p).toPath.extend t₀`, there is a sub-interval
`(a, b)` containing `t₀` such that on this open interval, the per-
fibre integrand at `u` is computable via the lifted-point sheet's
ambient `sheet_q.g ∘ β ∘ σ`. -/
theorem sourceFiberPath_integrand_eq_local_at_lifted_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
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
    let sheet_q := f.localSheetData_at_regular hnc hq_reg
    let f_pull : ℝ → X := fun u => sheet_q.g (β (Real.smoothTransition u))
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≤ t₀ ∧ t₀ ≤ b ∧
      (0 < t₀ → a < t₀) ∧ (t₀ < 1 → t₀ < b) ∧
      ∀ u ∈ Ioo a b,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).integrand om u
          = SmoothPath.applyCotangent (om (f_pull u))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) f_pull u :
                  ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (f_pull u)) (1 : ℝ)) := by
  classical
  intro γ q hβσt₀_reg hq_lift hq_reg sheet_q f_pull
  -- Apply the local identification chip.
  obtain ⟨a, b, ha_mem, hb_mem, ha_le_t₀, ht₀_le_b, ha_lt_t₀, ht₀_lt_b, h_eq_on⟩ :=
    f.sourceFiberPath_toPath_extend_eq_sheet_g_locally_at hnc hβ_smooth hβ_reg hx ht₀
  refine ⟨a, b, ha_mem, hb_mem, ha_le_t₀, ht₀_le_b, ha_lt_t₀, ht₀_lt_b, ?_⟩
  intro u hu
  -- The local identification gives γ u = sheet_q.g (β(σ u)) for u ∈ [a, b].
  -- This is exactly `f_pull u`.
  have h_ambient_eq : ∀ v, v ∈ Icc a b →
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).ambient v = f_pull v := by
    intro v hv
    -- v ∈ [a, b] ⊆ [0, 1], so v ∈ unitInterval.
    have hv_unit : v ∈ unitInterval :=
      ⟨le_trans ha_mem.1 hv.1, le_trans hv.2 hb_mem.2⟩
    -- ambient v = toPath ⟨v, hv_unit⟩ on unitInterval.
    have h_ambient :
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).ambient v
          = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨v, hv_unit⟩ :=
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).ambient_eq_on_unitInterval ⟨v, hv_unit⟩
    -- toPath ⟨v, hv_unit⟩ = toPath.extend v on unitInterval.
    have h_toPath_extend :
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨v, hv_unit⟩
          = (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend v :=
      (Path.extend_extends' (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath
        ⟨v, hv_unit⟩).symm
    rw [h_ambient, h_toPath_extend]
    exact h_eq_on v hv
  exact SmoothPath.integrand_eq_of_ambient_eqOn_Icc_fun h_ambient_eq om hu

end MeromorphicNonzero

end JacobianChallenge

end
