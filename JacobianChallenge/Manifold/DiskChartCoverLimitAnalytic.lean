/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverArzela
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option diagnostics.threshold 100

/-! # Analyticity of the chart limit on the open inner ball

For each base point `x ∈ basePoints` and the diagonal subsequence `ψ`
(chip 5c), the sequence `localCoeff (om_n (ψ k)) x : ℂ → ℂ` converges
uniformly on the inner closed disk to (the extension of) the BCF limit
`g_lim_x`. Restricted to the *open* inner ball, this is locally uniform
convergence on an open subset of `ℂ`, and each `localCoeff (om_n (ψ k))
x` is analytic on the chart target (which contains the ball). By
mathlib's `TendstoLocallyUniformlyOn.differentiableOn`, the limit is
`DifferentiableOn ℂ` on the open ball — equivalently, analytic
there.

This is the analyticity input for chip 5g's section construction.

## Main result

* `DiskChartCover.limit_differentiableOn_innerBall` — given the BCF
  limit at base point `x` from chip 5b/5c, the limit function (as a
  ℂ → ℂ map taking the value `g_lim_x ⟨w, hw⟩` on the closed disk
  and `0` outside) is `DifferentiableOn ℂ` on the open inner ball.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

open Classical in
/-- Extend a BCF on `↥(closedBall)` to a function `ℂ → ℂ` (with junk
value `0` outside the closed disk). -/
noncomputable def bcfExtend
    (cover : DiskChartCover X) {x : X}
    (g : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ) : ℂ → ℂ :=
  fun w =>
    if hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x) then
      g ⟨w, hw⟩
    else 0

omit [IsManifold 𝓘(ℂ) ω X] in
/-- At points of the closed disk, the extension agrees with the BCF. -/
lemma bcfExtend_apply (cover : DiskChartCover X) {x : X}
    (g : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    bcfExtend cover g w = g ⟨w, hw⟩ := by
  unfold bcfExtend
  rw [dif_pos hw]

/-- The BCF-metric distance between `localCoeffBcf cover om hx` and `g`
bounds the pointwise distance between `localCoeff om x` and the
extended `g` on the closed disk. -/
private lemma dist_localCoeff_bcfExtend_le (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    (g : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    dist (localCoeff om x w) (bcfExtend cover g w)
      ≤ dist (localCoeffBcf cover om hx) g := by
  rw [bcfExtend_apply cover g hw]
  have h_pt : dist ((localCoeffBcf cover om hx) ⟨w, hw⟩) (g ⟨w, hw⟩)
      ≤ dist (localCoeffBcf cover om hx) g :=
    BoundedContinuousFunction.dist_coe_le_dist _
  exact h_pt

/-- **Uniform convergence on the closed inner disk.** From chip 5b's
BCF convergence, get uniform convergence of `localCoeff (om_n k) x` to
`bcfExtend cover g_lim_x` on `closedBall (innerRadius_x)`. -/
private lemma tendstoUniformlyOn_localCoeff_closedBall
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {g_lim : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n k) hx) atTop (𝓝 g_lim)) :
    TendstoUniformlyOn (fun k => localCoeff (om_n k) x)
      (bcfExtend cover g_lim) atTop
      (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendsto_nhds] at h_tendsto
  have h_ε := h_tendsto ε hε
  rw [eventually_atTop] at h_ε
  obtain ⟨N, hN⟩ := h_ε
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro k hk_N w hw
  rw [dist_comm]
  calc dist (localCoeff (om_n k) x w) (bcfExtend cover g_lim w)
      ≤ dist (localCoeffBcf cover (om_n k) hx) g_lim :=
        dist_localCoeff_bcfExtend_le cover (om_n k) hx g_lim hw
    _ < ε := hN k hk_N

/-- **Locally uniform convergence on the open inner ball.** Subset of
the closed disk; restricts the previous uniform convergence. -/
private lemma tendstoLocallyUniformlyOn_localCoeff_ball
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {g_lim : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n k) hx) atTop (𝓝 g_lim)) :
    TendstoLocallyUniformlyOn (fun k => localCoeff (om_n k) x)
      (bcfExtend cover g_lim) atTop
      (ball ((chartAt ℂ x) x) (cover.innerRadius x)) := by
  have h_uniform :=
    tendstoUniformlyOn_localCoeff_closedBall cover om_n hx h_tendsto
  exact (h_uniform.mono ball_subset_closedBall).tendstoLocallyUniformlyOn

/-- **Differentiability of the limit on the open inner ball.** -/
theorem limit_differentiableOn_innerBall (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {g_lim : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n k) hx) atTop (𝓝 g_lim)) :
    DifferentiableOn ℂ (bcfExtend cover g_lim)
      (ball ((chartAt ℂ x) x) (cover.innerRadius x)) := by
  have h_loc :=
    tendstoLocallyUniformlyOn_localCoeff_ball cover om_n hx h_tendsto
  have h_diff : ∀ᶠ k in atTop,
      DifferentiableOn ℂ (localCoeff (om_n k) x)
        (ball ((chartAt ℂ x) x) (cover.innerRadius x)) := by
    refine Filter.Eventually.of_forall (fun k => ?_)
    have h_inner_le_outer :
        cover.innerRadius x ≤ cover.outerRadius x :=
      le_of_lt (cover.innerRadius_lt_outerRadius x hx)
    have h_subset :
        ball ((chartAt ℂ x) x) (cover.innerRadius x)
          ⊆ (chartAt ℂ x).target :=
      (ball_subset_closedBall.trans
        (closedBall_subset_closedBall h_inner_le_outer)).trans
        (cover.closedDisk_in_target x hx)
    exact (localCoeff_differentiableOn (om_n k) x).mono h_subset
  exact h_loc.differentiableOn h_diff isOpen_ball

/-- **Analyticity of the limit on the open inner ball.** Follows from
differentiability via `DifferentiableOn.analyticOn` on an open set in ℂ
(complex differentiability ⇒ analyticity). -/
theorem limit_analyticOn_innerBall (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {g_lim : BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n k) hx) atTop (𝓝 g_lim)) :
    AnalyticOn ℂ (bcfExtend cover g_lim)
      (ball ((chartAt ℂ x) x) (cover.innerRadius x)) :=
  (limit_differentiableOn_innerBall cover om_n hx h_tendsto).analyticOn
    isOpen_ball

end DiskChartCover

end JacobianChallenge

end
