/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen
import JacobianChallenge.Manifold.SmoothPathLinearInChart
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathConst
import JacobianChallenge.Manifold.SmoothPathConnected

set_option linter.unusedSectionVars false

/-! # Local smooth-path-connectedness on a complex 1-manifold

For every point `p : X` of a complex 1-manifold, there exists an open
neighborhood `U ∋ p` such that any two points of `U` are joined by a
smooth path. Construction:

1. Pick `φ := chartAt ℂ p` and `z := φ p ∈ φ.target`.
2. Pick `r > 0` with `Metric.ball z r ⊆ φ.target` (openness of
   `φ.target`).
3. Set `U := φ.source ∩ φ ⁻¹' Metric.ball z r`.

For any `q₁, q₂ ∈ U`, both `φ q₁` and `φ q₂` lie in the convex ball
`Metric.ball z r`. Hence the closed segment `segment ℝ (φ q₁) (φ q₂)`
lies in the ball (by `Convex.segment_subset` applied to
`convex_ball`), and thence in `φ.target`. The hypothesis of
`SmoothPath.linearInChartSegment` is discharged, producing a smooth
path between `q₁` and `q₂`.

This is the local building block for the chart-cover lift of
`SmoothPathConnected I X` on a connected complex 1-manifold: the open
`U` is a smoothly-path-connected neighborhood of every point, and a
standard open-closed argument turns local smooth-path-connectedness
into the global predicate.

No `sorry`, no `axiom`.
-/

noncomputable section

open Set Metric
open scoped Manifold Topology

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-- **Existence of a convex chart-ball neighborhood.** Every point of
a complex 1-manifold has an open neighborhood `U` (built as a chart
restricted to a Euclidean open ball in `ℂ`) inside which any two
points are joined by a smooth path. The smooth path is constructed by
pulling back the affine segment `(1 - σ t) • φ q₁ + σ t • φ q₂` (where
`σ = Real.smoothTransition`) under the chart inverse `φ.symm`. -/
theorem exists_smooth_path_connected_chart_nbhd (p : X) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      ∀ q₁ q₂ : X, q₁ ∈ U → q₂ ∈ U →
        ∃ γ : SmoothPath 𝓘(ℝ, ℂ) X, γ.src = q₁ ∧ γ.tgt = q₂ := by
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hφ_def
  have hp_src : p ∈ φ.source := mem_chart_source ℂ p
  set z : ℂ := φ p with hz_def
  have hz_target : z ∈ φ.target := φ.map_source hp_src
  -- Pick a Euclidean open ball around `z` contained in the open
  -- chart target.
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp φ.open_target z hz_target
  -- The candidate neighborhood `U := φ.source ∩ φ ⁻¹' Metric.ball z r`.
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball z r, ?_, ?_, ?_⟩
  · -- `U = φ.source ∩ φ ⁻¹' (Metric.ball z r)` is open by
    -- `ContinuousOn.isOpen_inter_preimage` (both `φ.source` and
    -- `Metric.ball z r` are open).
    exact φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source
      Metric.isOpen_ball
  · -- `p ∈ U`: `p ∈ φ.source` and `φ p = z ∈ ball z r` (with
    -- `0 < r`, by `Metric.mem_ball_self`).
    exact ⟨hp_src, Metric.mem_ball_self hr_pos⟩
  · -- Any two points of `U` are smoothly path-connected.
    intro q₁ q₂ hq₁ hq₂
    have hq₁_src : q₁ ∈ φ.source := hq₁.1
    have hq₂_src : q₂ ∈ φ.source := hq₂.1
    have hq₁_ball : φ q₁ ∈ Metric.ball z r := hq₁.2
    have hq₂_ball : φ q₂ ∈ Metric.ball z r := hq₂.2
    -- The closed segment `[φ q₁, φ q₂]` lies in the convex ball,
    -- hence in `φ.target`.
    have h_seg_in_ball : segment ℝ (φ q₁) (φ q₂) ⊆ Metric.ball z r :=
      (convex_ball z r).segment_subset hq₁_ball hq₂_ball
    have h_seg : segment ℝ (φ q₁) (φ q₂) ⊆ φ.target :=
      h_seg_in_ball.trans hr_sub
    have h_atlas : φ ∈ atlas ℂ X := chart_mem_atlas ℂ p
    refine ⟨SmoothPath.linearInChartSegment φ h_atlas q₁ q₂
              hq₁_src hq₂_src h_seg, ?_, ?_⟩
    · exact SmoothPath.linearInChartSegment_src φ h_atlas
        q₁ q₂ hq₁_src hq₂_src h_seg
    · exact SmoothPath.linearInChartSegment_tgt φ h_atlas
        q₁ q₂ hq₁_src hq₂_src h_seg

/-! ## Global discharge via the open-closed argument

The set of points reachable from a fixed `p : X` by a smooth path is
both open (via the local lemma + `concat`) and closed (the complement
is also open, by a symmetric argument). On a connected space, a
nonempty clopen subset is all of `X`, so every point is reachable
from `p`. -/

/-- **The reachable set from a base point.** All `q : X` such that
there exists a smooth path from `p` to `q`. -/
private def reachableFrom (p : X) : Set X :=
  {x | ∃ γ : SmoothPath 𝓘(ℝ, ℂ) X, γ.src = p ∧ γ.tgt = x}

private lemma p_mem_reachableFrom (p : X) : p ∈ reachableFrom p :=
  ⟨SmoothPath.const _ _ p, SmoothPath.const_src p, SmoothPath.const_tgt p⟩

/-- **`reachableFrom p` is open.** If `q ∈ reachableFrom p`, the local
smoothly-path-connected neighborhood of `q` is also in
`reachableFrom p`: every `q' ∈ U_q` is connected to `q` smoothly, and
the path `p → q` concatenates with `q → q'` (via
`SmoothPath.concat`). -/
private lemma reachableFrom_isOpen (p : X) : IsOpen (reachableFrom p) := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨γ_pq, hγ_pq_src, hγ_pq_tgt⟩ := hq
  obtain ⟨U, hU_open, hq_U, h_path⟩ :=
    exists_smooth_path_connected_chart_nbhd q
  refine ⟨U, ?_, hU_open, hq_U⟩
  intro q' hq'
  obtain ⟨γ_qq', hγ_qq'_src, hγ_qq'_tgt⟩ := h_path q q' hq_U hq'
  have h_eq : γ_pq.tgt = γ_qq'.src := by rw [hγ_pq_tgt, hγ_qq'_src]
  refine ⟨γ_pq.concat γ_qq' h_eq, ?_, ?_⟩
  · rw [SmoothPath.concat_src]; exact hγ_pq_src
  · rw [SmoothPath.concat_tgt]; exact hγ_qq'_tgt

/-- **The complement of `reachableFrom p` is open.** If `q ∉ reachableFrom p`,
take its local smoothly-path-connected neighborhood `U_q`. Any
`q' ∈ U_q` is connected smoothly to `q`; if `q'` were in
`reachableFrom p`, then composing `p → q'` with `q' → q` would give
`q ∈ reachableFrom p`, contradiction. -/
private lemma compl_reachableFrom_isOpen (p : X) :
    IsOpen (reachableFrom p)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨U, hU_open, hq_U, h_path⟩ :=
    exists_smooth_path_connected_chart_nbhd q
  refine ⟨U, ?_, hU_open, hq_U⟩
  intro q' hq' hq'_reach
  obtain ⟨γ_pq', hγ_pq'_src, hγ_pq'_tgt⟩ := hq'_reach
  obtain ⟨γ_q'q, hγ_q'q_src, hγ_q'q_tgt⟩ := h_path q' q hq' hq_U
  have h_eq : γ_pq'.tgt = γ_q'q.src := by rw [hγ_pq'_tgt, hγ_q'q_src]
  apply hq
  exact ⟨γ_pq'.concat γ_q'q h_eq,
    by rw [SmoothPath.concat_src]; exact hγ_pq'_src,
    by rw [SmoothPath.concat_tgt]; exact hγ_q'q_tgt⟩

/-- `reachableFrom p` is closed (the complement is open). -/
private lemma reachableFrom_isClosed (p : X) : IsClosed (reachableFrom p) :=
  isOpen_compl_iff.mp (compl_reachableFrom_isOpen p)

/-- `reachableFrom p` is clopen. -/
private lemma reachableFrom_isClopen (p : X) : IsClopen (reachableFrom p) :=
  ⟨reachableFrom_isClosed p, reachableFrom_isOpen p⟩

/-- **`SmoothPathConnected` on a connected complex 1-manifold.** The
open-closed argument: the reachable set from any base point `p` is
clopen and nonempty (contains `p`), hence by connectedness equals all
of `X`. -/
theorem smoothPathConnected_of_preconnected [PreconnectedSpace X] :
    SmoothPathConnected 𝓘(ℝ, ℂ) X := by
  intro p q
  have h_clopen : IsClopen (reachableFrom p) := reachableFrom_isClopen p
  have h_nonempty : (reachableFrom p).Nonempty :=
    ⟨p, p_mem_reachableFrom p⟩
  have h_univ : reachableFrom p = Set.univ :=
    h_clopen.eq_univ h_nonempty
  have hq_reach : q ∈ reachableFrom p := by
    rw [h_univ]; trivial
  exact hq_reach

end JacobianChallenge

end
