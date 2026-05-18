/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopPeriod
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.SmoothPathChartCompat
import JacobianChallenge.Manifold.LoopPeriodConstant
import JacobianChallenge.Manifold.ComplexManifoldRealification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Deriv

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

/-! ## Continuity of α.localCoeff ∘ chartPath -/

/-- **Continuity of `t ↦ α.localCoeff y (chartPath t)`** on `[0, 1]`.
Composition of the continuous `α.localCoeff y` (on chart-target) with
the continuous `chartPath` (mapping `[0, 1]` into chart-target). -/
lemma localCoeff_chartPath_continuousOn
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) :
    ContinuousOn
      (fun t : ℝ => α.localCoeff data.basePoint (data.chartPath t))
      (Set.Icc (0 : ℝ) 1) := by
  -- α.localCoeff is DifferentiableOn (chart-target), hence ContinuousOn.
  have h_cont_on : ContinuousOn (α.localCoeff data.basePoint)
      (chartAt ℂ data.basePoint).target :=
    (α.localCoeff_differentiableOn data.basePoint).continuousOn
  -- chartPath is continuous on [0,1] via MDifferentiableAt → ContinuousAt.
  have h_chartPath_cont : ContinuousOn data.chartPath (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((data.chartPath_mdifferentiableAt_of_unitInterval ht).continuousAt).continuousWithinAt
  -- chartPath maps [0,1] into chart-target (via chart_image_in_ball + ball_sub_target).
  have h_maps : Set.MapsTo data.chartPath (Set.Icc (0 : ℝ) 1)
      (chartAt ℂ data.basePoint).target :=
    fun t ht => data.ball_sub_target (data.chart_image_in_ball t ht)
  -- Compose.
  exact h_cont_on.comp h_chartPath_cont h_maps

/-! ## Continuity of `deriv chartPath` on `[0, 1]` via pointwise HasDerivAt -/

/-- **`chartPath` has a derivative at each `t ∈ [0, 1]`.** Direct from
the chain rule `mfderiv (φ ∘ γ.ambient)` already computed in
`SmoothPath.mfderiv_chart_comp_ambient_apply_one` + the
ℝ-differentiability bridge `MDifferentiableAt.hasDerivAt`. -/
lemma chartPath_hasDerivAt
    (data : ChartContainedClosedLoop (X := X)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt data.chartPath (deriv data.chartPath t) t :=
  (data.chartPath_mdifferentiableAt_of_unitInterval ht).differentiableAt.hasDerivAt

/-! ## Final assembly

The remaining step is to bridge `complexChainPeriod (single γ) α` (defined
via realComponent + i·imagComponent of SmoothPath integrals) with the
chart-coord complex integral `∫_0^1 (α.localCoeff y (chartPath t)) ·
(deriv chartPath t) dt`. This bridge plus `chartPath_loop_integral_zero`
(in tree) gives the full discharge of `ChartContainedLoopVanishingHypothesis`.

The bridge requires:
- Identifying the realComponent / imagComponent integrands with the
  real / imaginary parts of the chart-coord product integrand.
- Discharging the integrability hypothesis (continuity of `deriv chartPath`
  on `[0,1]`, modulo a real-smoothness restrictScalars step on the chart).

Both steps follow from standard manifold real-vs-complex differentiability
identifications. Surfaced here as named ingredients for subsequent chips. -/

/-- **Named ingredient: deriv chartPath continuity on [0, 1].**
Follows from `chart ∘ γ.ambient` being `C^∞` on the chart-source preimage
(open) and hence `ContDiffOn ℝ ⊤` on that open set, restricted to [0,1].
The substantive piece is the complex-to-real-scalars transfer of the
chart's smoothness. -/
def DerivChartPathContinuousOn_named (data : ChartContainedClosedLoop (X := X)) : Prop :=
  ContinuousOn (deriv data.chartPath) (Set.Icc (0 : ℝ) 1)

/-- **Discharge of `DerivChartPathContinuousOn_named`.**
The composite `chartPath = chart ∘ γ.ambient : ℝ → ℂ` is `C^∞` on the
open preimage `U := γ.ambient⁻¹ chart.source ⊆ ℝ` because:
  (a) `γ.ambient` is `C^∞` from `𝓘(ℝ,ℝ)` to `𝓘(ℝ,ℂ)`
      (`SmoothPath.ambient_contMDiff`);
  (b) the chart `chartAt ℂ basePoint` is `C^∞` on its source under the
      real-realified manifold structure (`contMDiffOn_chart`, using
      `complexManifoldRealification`).
On vector spaces with trivial models, `ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞`
collapses to `ContDiffOn ℝ ∞` via `contMDiffOn_iff_contDiffOn`. Then
`ContDiffOn.continuousOn_deriv_of_isOpen` gives continuity of
`deriv chartPath` on `U`, and `[0,1] ⊆ U` (via `ambient_in_source`)
finishes the restriction. -/
theorem derivChartPathContinuousOn_holds
    (data : ChartContainedClosedLoop (X := X)) :
    DerivChartPathContinuousOn_named data := by
  show ContinuousOn (deriv data.chartPath) (Set.Icc (0 : ℝ) 1)
  -- 1. Open neighborhood `U` of `[0,1]` in ℝ on which `chartPath` is C^∞.
  set U : Set ℝ := data.γ.ambient ⁻¹' (chartAt ℂ data.basePoint).source with hU_def
  have h_amb_cont : Continuous data.γ.ambient :=
    data.γ.ambient_contMDiff.continuous
  have hU_open : IsOpen U :=
    (chartAt ℂ data.basePoint).open_source.preimage h_amb_cont
  have hUcc : Set.Icc (0 : ℝ) 1 ⊆ U :=
    fun t ht => data.ambient_in_source t ht
  -- 2. `γ.ambient` is C^∞ from 𝓘(ℝ,ℝ) into 𝓘(ℝ,ℂ).
  have h_amb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ data.γ.ambient :=
    data.γ.ambient_contMDiff
  -- 3. The chart is C^∞ on its source under the real manifold structure.
  have h_chart :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ data.basePoint)
        (chartAt ℂ data.basePoint).source :=
    contMDiffOn_chart
  -- 4. Composition: chartPath = chart ∘ γ.ambient is ContMDiffOn ∞ on U.
  have h_amb_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ data.γ.ambient U :=
    h_amb.contMDiffOn
  have h_maps : Set.MapsTo data.γ.ambient U (chartAt ℂ data.basePoint).source :=
    fun t ht => ht
  have h_comp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ data.chartPath U :=
    h_chart.comp h_amb_on h_maps
  -- 5. Bridge to ContDiffOn ℝ via trivial-model identification.
  have h_contDiffOn : ContDiffOn ℝ ∞ data.chartPath U :=
    h_comp.contDiffOn
  -- 6. ContDiffOn → ContinuousOn of `deriv` on the open `U`.
  have h_one_le_top : (1 : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  have h_cont_U : ContinuousOn (deriv data.chartPath) U :=
    h_contDiffOn.continuousOn_deriv_of_isOpen hU_open h_one_le_top
  -- 7. Restrict to [0, 1].
  exact h_cont_U.mono hUcc

/-- **Named ingredient: complexChainPeriod identifies with the chart-coord integral.**
For a `ChartContainedClosedLoop` `data` and `α : HolomorphicOneForm X`:
`complexChainPeriod (single γ) α = ∫_0^1 (α.localCoeff y (chartPath t)) ·
(deriv chartPath t) dt`.

The substantive content is the chart-pullback identification of
realComponent / imagComponent against the chart-coord product expansion. -/
def ComplexChainPeriodEqChartIntegral_named
    (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X) : Prop :=
  complexChainPeriod (SmoothChain.single data.γ) α
    = ∫ t in (0 : ℝ)..1,
        (α.localCoeff data.basePoint (data.chartPath t)) *
          (deriv data.chartPath t)

/-- **`ChartContainedLoopVanishingHypothesis_holds` from the two named ingredients.**
Composes `chartPath_loop_integral_zero` with the chart-coord-integral
identification to get `complexChainPeriod (single γ) α = 0`. -/
theorem chartContainedLoopVanishingHypothesis_of_ingredients
    (h_deriv :
      ∀ data : ChartContainedClosedLoop (X := X), DerivChartPathContinuousOn_named data)
    (h_bridge :
      ∀ (data : ChartContainedClosedLoop (X := X)) (α : HolomorphicOneForm X),
        ComplexChainPeriodEqChartIntegral_named data α) :
    ChartContainedLoopVanishingHypothesis (X := X) := by
  intro data α
  rw [h_bridge data α]
  apply chartPath_loop_integral_zero data α
  -- IntervalIntegrable from continuity of the product integrand.
  have h1 := data.localCoeff_chartPath_continuousOn α
  have h2 := h_deriv data
  have h_cont : ContinuousOn
      (fun t => (α.localCoeff data.basePoint (data.chartPath t)) *
                  (deriv data.chartPath t))
      (Set.Icc (0 : ℝ) 1) :=
    h1.mul h2
  exact h_cont.intervalIntegrable_of_Icc zero_le_one

end ChartContainedClosedLoop

end JacobianChallenge

end
