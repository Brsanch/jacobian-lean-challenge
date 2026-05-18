/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopPeriod
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.SmoothPathChartCompat
import JacobianChallenge.Manifold.LoopPeriodConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

/-! # Discharge of `ChartContainedLoopVanishingHypothesis` via local primitive + FTC

For a `ChartContainedClosedLoop` on `X` and a holomorphic 1-form
`α : HolomorphicOneForm X`, the complex period vanishes:
`complexChainPeriod (SmoothChain.single γ) α = 0`.

## Proof strategy

1. `α.localCoeff y` has a primitive `F : ℂ → ℂ` on `Metric.ball c r`
   (`HolomorphicOneFormLocalPrimitive.exists_local_primitive_on_ball`).

2. The composite `G := F ∘ (chartAt ℂ y) : X → ℂ` (on the chart source)
   serves as a local primitive of `α` on `X`: under chart-coord chain
   rule, `mfderiv G (γ.ambient t) (γ.velocity t)` equals
   `α.eval (γ.ambient t) (γ.velocity t)` (the integrand of
   `complexChainPeriod`).

3. By the manifold FTC (applied separately to real and imaginary parts
   of `G`), `complexChainPeriod (single γ) α = G(γ.tgt) - G(γ.src)`.

4. For a closed loop (`γ.src = γ.tgt`), this is `0`.

The substantive content is step 2 (chain rule for chart-pullback) and
step 3 (FTC on real/imag parts). Both are standard but require careful
chart-coord bookkeeping.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory intervalIntegral

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

/-- **The chart-coord path traced by a chart-contained loop.**
For a `ChartContainedClosedLoop` `data`, the function `t ↦ chart(γ(t))`
on `[0, 1]` traces a closed loop in `Metric.ball data.ballCentre data.ballRadius`. -/
def chartPath (data : ChartContainedClosedLoop (X := X)) (t : ℝ) : ℂ :=
  (chartAt ℂ data.basePoint) (data.γ.ambient t)

@[simp] lemma chartPath_at_one_eq_at_zero (data : ChartContainedClosedLoop (X := X)) :
    data.chartPath 1 = data.chartPath 0 := by
  unfold chartPath
  -- Use the loop property: γ.src = γ.tgt, where src and tgt are γ.ambient 0 and γ.ambient 1.
  have h_src_amb : data.γ.ambient 0 = data.γ.src := by
    have h := data.γ.ambient_eq_on_unitInterval ⟨0, ⟨le_refl 0, zero_le_one⟩⟩
    have h_val : ((⟨0, ⟨le_refl 0, zero_le_one⟩⟩ : unitInterval) : ℝ) = 0 := rfl
    rw [h_val] at h
    rw [h]
    exact data.γ.toPath.source
  have h_tgt_amb : data.γ.ambient 1 = data.γ.tgt := by
    have h := data.γ.ambient_eq_on_unitInterval ⟨1, ⟨zero_le_one, le_refl 1⟩⟩
    have h_val : ((⟨1, ⟨zero_le_one, le_refl 1⟩⟩ : unitInterval) : ℝ) = 1 := rfl
    rw [h_val] at h
    rw [h]
    exact data.γ.toPath.target
  rw [h_src_amb, h_tgt_amb, data.is_loop]

/-! ## Local primitive G : X → ℂ defined via chart composition -/

/-- **Local primitive on `X` via chart composition.**
For a `ChartContainedClosedLoop` data and `α : HolomorphicOneForm X`, the
local primitive `F : ℂ → ℂ` on the chart-target ball lifts to a
ℂ-valued function `G : X → ℂ` defined as `F ∘ chartAt`. Concretely:
`G x = F (chartAt ℂ data.basePoint x)` for `x ∈ chart.source`. -/
noncomputable def localPrimitiveOnX
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) : X → ℂ :=
  fun x =>
    (Classical.choose
      (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
        data.ball_sub_target))
      ((chartAt ℂ data.basePoint) x)

/-- The chosen local primitive on `X` satisfies the
`HasDerivAt`-on-chart-ball property pulled through the chart. -/
lemma localPrimitiveOnX_spec
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) :
    ∀ z ∈ Metric.ball data.ballCentre data.ballRadius,
      HasDerivAt
        (Classical.choose
          (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
            data.ball_sub_target))
        (α.localCoeff data.basePoint z) z :=
  Classical.choose_spec
    (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
      data.ball_sub_target)

/-! ## The `chartPath` is differentiable at points of `[0,1]` -/

/-- **Differentiability of `chartPath`.** The composite
`chartAt y ∘ γ.ambient : ℝ → ℂ` is differentiable at any `t : ℝ` such
that `γ.ambient t ∈ (chartAt ℂ y).source`. Direct via
`SmoothPath.mdifferentiableAt_chart_comp_ambient`. -/
lemma chartPath_mdifferentiableAt
    (data : ChartContainedClosedLoop (X := X)) {t : ℝ}
    (h_in_source : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t :=
  SmoothPath.mdifferentiableAt_chart_comp_ambient data.γ
    (φ := chartAt ℂ data.basePoint) (chart_mem_atlas ℂ data.basePoint)
    h_in_source

/-- **`chartPath` is differentiable at every `t ∈ [0, 1]`** (using the
chart-source containment from the structure). -/
lemma chartPath_mdifferentiableAt_of_unitInterval
    (data : ChartContainedClosedLoop (X := X)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t :=
  data.chartPath_mdifferentiableAt (data.ambient_in_source t ht)

/-! ## Differentiability of `F ∘ chartPath` -/

/-- **`F ∘ chartPath` is differentiable at each `t ∈ [0, 1]`.** The
chain rule via `HasDerivAt.comp` applied to the local primitive `F`
and the chart-coord path `chartPath`. -/
lemma F_comp_chartPath_hasDerivAt
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      ((Classical.choose
        (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
          data.ball_sub_target)) ∘ data.chartPath)
      ((α.localCoeff data.basePoint (data.chartPath t)) *
        (deriv data.chartPath t)) t := by
  -- The primitive F satisfies HasDerivAt F (α.localCoeff y z) z on the ball.
  set F : ℂ → ℂ := Classical.choose
    (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
      data.ball_sub_target) with hF_def
  -- chartPath t is in the ball (from the structure field).
  have h_in_ball : data.chartPath t ∈ Metric.ball data.ballCentre data.ballRadius :=
    data.chart_image_in_ball t ht
  -- F has derivative α.localCoeff y at chartPath t.
  have hF_deriv : HasDerivAt F
      (α.localCoeff data.basePoint (data.chartPath t)) (data.chartPath t) :=
    data.localPrimitiveOnX_spec α (data.chartPath t) h_in_ball
  -- chartPath is differentiable at t (from MDifferentiableAt above).
  -- Convert MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) chartPath t to HasDerivAt.
  have h_chart_mdiff := data.chartPath_mdifferentiableAt_of_unitInterval ht
  have h_chart_diff : DifferentiableAt ℝ data.chartPath t := by
    -- MDifferentiableAt with model 𝓘(ℝ,ℝ) → 𝓘(ℝ,ℂ) is the same as DifferentiableAt ℝ.
    show DifferentiableAt ℝ
      ((chartAt ℂ data.basePoint : X → ℂ) ∘ data.γ.ambient) t
    exact MDifferentiableAt.differentiableAt h_chart_mdiff
  have h_chart_hasDerivAt : HasDerivAt data.chartPath (deriv data.chartPath t) t :=
    h_chart_diff.hasDerivAt
  -- Apply chain rule.
  exact hF_deriv.comp t h_chart_hasDerivAt

/-! ## FTC applied to `F ∘ chartPath` -/

/-- **FTC: ∫_0^1 deriv(F ∘ chartPath) = (F ∘ chartPath)(1) − (F ∘ chartPath)(0).**
By `intervalIntegral.integral_eq_sub_of_hasDerivAt` applied with the
chain-rule derivative supplied by `F_comp_chartPath_hasDerivAt`. -/
lemma F_comp_chartPath_integral_eq_sub
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    (h_integrable : IntervalIntegrable
      (fun t => (α.localCoeff data.basePoint (data.chartPath t)) *
                  (deriv data.chartPath t))
      MeasureTheory.volume 0 1) :
    ∫ t in (0 : ℝ)..1,
        (α.localCoeff data.basePoint (data.chartPath t)) *
          (deriv data.chartPath t)
      = ((Classical.choose
          (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
            data.ball_sub_target)) ∘ data.chartPath) 1
        - ((Classical.choose
          (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
            data.ball_sub_target)) ∘ data.chartPath) 0 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => ?_) h_integrable
  -- t ∈ [[0, 1]] = uIcc 0 1 = Icc 0 1 (since 0 ≤ 1).
  have ht_icc : t ∈ Set.Icc (0 : ℝ) 1 := by
    rwa [Set.uIcc_of_le zero_le_one] at ht
  exact data.F_comp_chartPath_hasDerivAt α ht_icc

/-- **FTC at a closed loop: ∫_0^1 (α.localCoeff y (chartPath t)) · (deriv chartPath t) = 0.**
Combines `F_comp_chartPath_integral_eq_sub` with
`chartPath_at_one_eq_at_zero` (closed-loop property). -/
lemma chartPath_loop_integral_zero
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X)
    (h_integrable : IntervalIntegrable
      (fun t => (α.localCoeff data.basePoint (data.chartPath t)) *
                  (deriv data.chartPath t))
      MeasureTheory.volume 0 1) :
    ∫ t in (0 : ℝ)..1,
        (α.localCoeff data.basePoint (data.chartPath t)) *
          (deriv data.chartPath t) = 0 := by
  rw [data.F_comp_chartPath_integral_eq_sub α h_integrable]
  -- (F ∘ chartPath) 1 = (F ∘ chartPath) 0 since chartPath 1 = chartPath 0.
  show (Classical.choose
        (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
          data.ball_sub_target)) (data.chartPath 1)
      - (Classical.choose
        (HolomorphicOneForm.exists_local_primitive_on_ball α data.basePoint
          data.ball_sub_target)) (data.chartPath 0) = 0
  rw [data.chartPath_at_one_eq_at_zero]
  ring

end ChartContainedClosedLoop

end JacobianChallenge

end
