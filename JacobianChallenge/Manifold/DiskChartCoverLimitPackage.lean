/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverLimitContMDiff
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

set_option diagnostics.threshold 100

/-! # Package the limit section as a `HolomorphicOneForm X`

For each base point `x ∈ basePoints` and `y` in chart-`x` preimage of
the *open* inner ball, mathlib's `Trivialization.contMDiffAt_section_iff`
(applied to the canonical trivialization `localTriv (achart x)` of the
cotangent bundle, which is automatically in the trivialization atlas as
`trivializationAt _ x`) converts section smoothness at `y` to smoothness
of the chart-`x`-frame snd component at `y`.

By chip 5h, the snd component equals `smulRight 1 (bcfExtend cover
g_lim_x ((chartAt ℂ x) y'))` on chart-`x` preimage of the *closed* inner
disk. On a neighbourhood of `y` (= chart-`x` preimage of the open inner
ball, which is open in `X` and contained in the closed-disk preimage),
the identification holds. By chip 5i, the RHS is `ContMDiffAt` at `y`.

Combining via `ContMDiffAt.congr_of_eventuallyEq`, the section is
`ContMDiffAt` at `y`. By the cover, every `y ∈ X` is in some
chart-`x` preimage of the open inner ball, hence the section is
`ContMDiff` on all of `X`.

This packages the limit as `HolomorphicOneForm X = ContMDiffSection
𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ))`.

## Main definition

* `DiskChartCover.limitHolomorphicOneForm` — the limit section as an
  honest `HolomorphicOneForm X`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The chart-`x` preimage of the open inner ball is open in `X`. -/
private lemma chart_preimage_ball_open (cover : DiskChartCover X) (x : X) :
    IsOpen ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹'
      (ball ((chartAt ℂ x) x) (cover.innerRadius x))) :=
  (chartAt ℂ x).continuousOn.isOpen_inter_preimage
    (chartAt ℂ x).open_source Metric.isOpen_ball

/-- **Section smoothness at any `y ∈ X`.**

Given the diagonal subsequence convergent at every base point, the
limit section is `ContMDiffAt` at every `y ∈ X`. -/
theorem limitSection_contMDiffAt
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    (y : X) :
    ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y' : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y'
        (limitSectionToFun cover om_n h_diag y')) y := by
  set x := chosenBasePoint cover y with hx_def
  have hx_mem : x ∈ cover.basePoints := chosenBasePoint_mem cover y
  have hy_source : y ∈ (chartAt ℂ x).source := chosenBasePoint_source cover y
  have hy_in_ball : (chartAt ℂ x) y ∈
      ball ((chartAt ℂ x) x) (cover.innerRadius x) :=
    chosenBasePoint_chartImage_in_ball cover y
  obtain ⟨g_lim_x, h_tendsto⟩ := h_diag x hx_mem
  -- Apply mathlib's bridge with the canonical trivialization at x.
  have h_y_baseSet : y ∈ (trivializationAt (ℂ →L[ℂ] ℂ)
      (CotangentSpace 𝓘(ℂ, ℂ)) x).baseSet := by
    show y ∈ ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).localTrivAt x).baseSet
    show y ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ x)
    show y ∈ (achart ℂ x).1.source
    rw [achart_val]
    exact hy_source
  rw [(trivializationAt (ℂ →L[ℂ] ℂ)
    (CotangentSpace 𝓘(ℂ, ℂ)) x).contMDiffAt_section_iff h_y_baseSet]
  -- Now need: ContMDiffAt of (fun x' => (e ⟨x', limitSectionToFun ... x'⟩).2) at y.
  -- The snd is `coordChange (achart x') (achart x) x' (limitSectionToFun x')`
  -- (per `localTriv_apply`).
  -- By chip 5h, on chart-x preimage of CLOSED inner disk, this equals
  -- `smulRight 1 (bcfExtend cover g_lim_x ((chartAt ℂ x) x'))`.
  -- A nbhd of y is in chart-x preimage of OPEN inner ball, hence in the
  -- closed-disk preimage.
  set U := (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹'
    (ball ((chartAt ℂ x) x) (cover.innerRadius x)) with hU_def
  have hU_open : IsOpen U := chart_preimage_ball_open cover x
  have hy_in_U : y ∈ U := ⟨hy_source, hy_in_ball⟩
  have h_eventually :
      (fun y' : X => (trivializationAt (ℂ →L[ℂ] ℂ)
          (CotangentSpace 𝓘(ℂ, ℂ)) x
        ⟨y', limitSectionToFun cover om_n h_diag y'⟩).2)
        =ᶠ[𝓝 y]
      (fun y' : X => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (bcfExtend cover g_lim_x ((chartAt ℂ x) y'))) := by
    filter_upwards [hU_open.mem_nhds hy_in_U] with y' hy'
    have hy'_source : y' ∈ (chartAt ℂ x).source := hy'.1
    have hy'_ball : (chartAt ℂ x) y' ∈
        ball ((chartAt ℂ x) x) (cover.innerRadius x) := hy'.2
    have hy'_closedBall : (chartAt ℂ x) y' ∈
        closedBall ((chartAt ℂ x) x) (cover.innerRadius x) :=
      ball_subset_closedBall hy'_ball
    -- snd of trivializationAt equals coordChange.
    have h_snd_eq :
        (trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace 𝓘(ℂ, ℂ)) x
          ⟨y', limitSectionToFun cover om_n h_diag y'⟩).2
        = ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y') (achart ℂ x) y'
          (limitSectionToFun cover om_n h_diag y')) :=
      cotangentBundle_trivializationAt_snd_apply
        (limitSectionToFun cover om_n h_diag) x y'
    rw [h_snd_eq]
    rw [chartFrame_limit_eq_smulRight cover om_n h_diag hx_mem y' hy'_source
      hy'_closedBall h_tendsto]
    rw [bcfExtend_apply cover g_lim_x hy'_closedBall]
  -- Apply chip 5i to get ContMDiffAt of the RHS.
  have h_rhs_contMDiff :=
    composed_smulRight_bcfExtend_contMDiffAt cover (fun k => om_n (ψ k)) hx_mem
      h_tendsto hy_source hy_in_ball
  -- Conclude via congr_of_eventuallyEq.
  exact h_rhs_contMDiff.congr_of_eventuallyEq h_eventually

/-- **Section smoothness on all of `X`.** -/
theorem limitSection_contMDiff
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim)) :
    ContMDiff 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y
        (limitSectionToFun cover om_n h_diag y)) :=
  fun y => limitSection_contMDiffAt cover om_n h_diag y

/-- **Package the limit as a `HolomorphicOneForm X`.** -/
noncomputable def limitHolomorphicOneForm
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim)) :
    HolomorphicOneForm X where
  toFun := limitSectionToFun cover om_n h_diag
  contMDiff_toFun := limitSection_contMDiff cover om_n h_diag

@[simp]
theorem limitHolomorphicOneForm_toFun
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    (y : X) :
    (limitHolomorphicOneForm cover om_n h_diag).toFun y
      = limitSectionToFun cover om_n h_diag y := rfl

end DiskChartCover

end JacobianChallenge

end
