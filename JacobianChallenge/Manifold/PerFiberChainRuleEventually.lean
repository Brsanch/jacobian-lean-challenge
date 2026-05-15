/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandPullback
import JacobianChallenge.Manifold.SheetGRealSmoothEventually

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-fibre chain rule in eventually form

`sourceFiberPath_integrand_eq_cotangentPullbackAt_apply` returns a
`δ_x > 0` such that on `Ioo 0 δ_x`, the per-fibre chain-rule identity
holds (given the per-`t` realified sheet smoothness as a hypothesis).
This file packages that as an `eventually` statement near `t = 0`,
discharging the realified-smoothness hypothesis via
`eventually_sheet_g_real_smooth`.

## What ships

* `MeromorphicNonzero.eventually_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply`
  — per-fibre filter form.

* `MeromorphicNonzero.eventually_forall_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply`
  — uniform-over-`sourceFiber` filter form.

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

/-- **Per-fibre chain rule eventually near `t = 0`.** -/
theorem eventually_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).integrand om t
        = SmoothPath.applyCotangent
            (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue
                  (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
              (β (Real.smoothTransition t)) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  (β (Real.smoothTransition t)))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                  ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  classical
  -- Extract δ from the per-fibre chain-rule chip.
  obtain ⟨δ, hδ_pos, _, hδ_id⟩ :=
    f.sourceFiberPath_integrand_eq_cotangentPullbackAt_apply hnc hβ_smooth hβ_reg hx om
  -- Realified smoothness eventually in 𝓝 0.
  have h_smooth_ev := f.eventually_sheet_g_real_smooth hnc hβ_smooth hβ_reg hx
  -- Promote to 𝓝[>] 0.
  have h_smooth_pos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
        (β (Real.smoothTransition t)) :=
    nhdsWithin_le_nhds h_smooth_ev
  -- `Ioo 0 δ ∈ 𝓝[>] 0`.
  have h_Ioo_nhds : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ_pos
  filter_upwards [h_smooth_pos, h_Ioo_nhds] with t h_smooth_t h_Ioo_t
  exact hδ_id t h_Ioo_t h_smooth_t

/-- **Uniform-over-`sourceFiber` form of per-fibre chain rule eventually.** -/
theorem eventually_forall_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ p : { x : X // x ∈ f.sourceFiber
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)).integrand om t
          = SmoothPath.applyCotangent
              (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
                (f.localSheetData_at_regular hnc
                  (f.mem_regularSet_of_preimage_regularValue
                    (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
                    ((f.mem_sourceFiber_iff
                      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).g
                (β (Real.smoothTransition t)) om)
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                  ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                    (β (Real.smoothTransition t)))
                ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                    ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  classical
  rw [Filter.eventually_all]
  intro p
  exact f.eventually_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    hnc hβ_smooth hβ_reg om
    ((f.mem_sourceFiber_iff
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)

end MeromorphicNonzero

end JacobianChallenge

end
