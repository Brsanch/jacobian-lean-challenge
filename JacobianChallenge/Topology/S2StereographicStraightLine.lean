/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2PuncturedSimplyConnected
import JacobianChallenge.Topology.S2EquatorialBeltPathConnected
import Mathlib.Analysis.Convex.Segment

/-! # Stereographic "straight line" paths inside a chart

Building block for polygonal approximation of `StandardS2`-valued loops.
Given two points `p, q : sphere 0 1` lying in `(stereographic hv).source`,
their stereographic images live in `(ℝ ∙ v)ᗮ`. The line segment between
these images in the orthogonal complement, pulled back through
`(stereographic hv).symm`, gives a canonical continuous path
`stereographicStraightLine v hv p q hp hq : Path p q` whose image
lies entirely in `(stereographic hv).source`.

Why this matters for the Phase-3 smoothing arc:

* Each `stereographicStraightLine` has image equal to the
  `(stereographic hv).symm`-image of a line segment in `(ℝ ∙ v)ᗮ`.
  Line segments are convex 1-dimensional subsets of the 2-dimensional
  `(ℝ ∙ v)ᗮ` — Baire-nowhere-dense. Their stereographic pullbacks are
  nowhere-dense compact arcs in `(stereographic hv).source ⊂ S²`.
* A polygonal approximation `γ'` of `γ` — built by concatenating
  `stereographicStraightLine`s subdivided per `exists_chart_indexed_partition`
  — has image equal to the union of finitely many nowhere-dense arcs,
  hence is itself nowhere-dense in `S²`. In particular `range γ' ≠ univ`,
  which is exactly `EveryS2LoopHomotopicToNonSurjective`.

This chip stops at the path construction and its in-chart simple-
connectedness consequence; the Baire / dimension argument is the
next chip's job.

## What is proved

* `stereographicStraightLine v hv p q hp hq : Path p q` — the
  canonical "straight line" path between two source points,
  via stereographic pullback of the (ℝ ∙ v)ᗮ line segment.
* `stereographicStraightLine_image_subset_source` — its image is
  contained in `(stereographic hv).source`.
* `stereographicStraightLine_homotopic` — given any path `γ : Path p q`
  whose image lies in `(stereographic hv).source`, that path is
  `Path.Homotopic` to `stereographicStraightLine v hv p q hp hq`. The
  homotopy lives in the simply-connected `S2Punctured v hv`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set Topology

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)

/-! ## Construction -/

/-- The "straight line" path from `p` to `q` inside the source of the
stereographic chart at `v`: pull back the linear interpolation
`(1 - t) • (stereographic hv p) + t • (stereographic hv q)` in
`(ℝ ∙ v)ᗮ` via `(stereographic hv).symm`. -/
def stereographicStraightLine
    (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hp : p ∈ (stereographic hv).source)
    (hq : q ∈ (stereographic hv).source) :
    Path p q where
  toFun t :=
    (stereographic hv).symm
      ((1 - (t : ℝ)) • (stereographic hv p) + (t : ℝ) • (stereographic hv q))
  continuous_toFun := by
    have h_cont_symm :
        ContinuousOn ((stereographic hv).symm) (stereographic hv).target :=
      (stereographic hv).continuousOn_symm
    rw [stereographic_target hv] at h_cont_symm
    have h_cont_symm' : Continuous ((stereographic hv).symm : (ℝ ∙ v)ᗮ → _) :=
      continuousOn_univ.mp h_cont_symm
    refine h_cont_symm'.comp ?_
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub
        (continuous_subtype_val.comp continuous_id)).smul continuous_const
    · exact (continuous_subtype_val.comp continuous_id).smul continuous_const
  source' := by
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h0]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact (stereographic hv).left_inv hp
  target' := by
    have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [h1]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact (stereographic hv).left_inv hq

/-! ## Image is contained in the source -/

/-- For every `t : unitInterval`, the straight-line interpolation
`(stereographicStraightLine ...) t` lies in `(stereographic hv).source`.
This follows because `(stereographic hv).symm` maps its target
`= univ` into its source. -/
theorem stereographicStraightLine_apply_mem_source
    {p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hp : p ∈ (stereographic hv).source)
    (hq : q ∈ (stereographic hv).source)
    (t : unitInterval) :
    (stereographicStraightLine hv p q hp hq) t ∈ (stereographic hv).source := by
  show (stereographic hv).symm _ ∈ _
  apply (stereographic hv).map_target
  rw [stereographic_target hv]
  exact Set.mem_univ _

/-- The full image of `stereographicStraightLine` is contained in the
source of the stereographic chart at `v`. -/
theorem stereographicStraightLine_range_subset_source
    {p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hp : p ∈ (stereographic hv).source)
    (hq : q ∈ (stereographic hv).source) :
    Set.range (stereographicStraightLine hv p q hp hq) ⊆
      (stereographic hv).source := by
  rintro _ ⟨t, rfl⟩
  exact stereographicStraightLine_apply_mem_source hv hp hq t

/-! ## In-chart homotopy uniqueness -/

/-- Any path `γ : Path p q` with image in `(stereographic hv).source` is
`Path.Homotopic` to the canonical `stereographicStraightLine`.

Proof: lift both paths to the subtype `S2Punctured v hv`, invoke
`SimplyConnectedSpace.paths_homotopic` from chip 2
(`S2Punctured.instSimplyConnectedSpace`), and map the resulting
homotopy back through the inclusion `S2Punctured v hv ↪ StandardS2`. -/
theorem stereographicStraightLine_homotopic
    {p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hp : p ∈ (stereographic hv).source)
    (hq : q ∈ (stereographic hv).source)
    (γ : Path p q)
    (h_image : ∀ t : unitInterval, γ t ∈ (stereographic hv).source) :
    γ.Homotopic (stereographicStraightLine hv p q hp hq) := by
  -- Lift γ and stereographicStraightLine to S2Punctured v hv.
  set γ' : Path (⟨p, hp⟩ : S2Punctured v hv) ⟨q, hq⟩ :=
    S2Punctured.liftPath hv hp hq γ h_image with hγ'_def
  set δ' : Path (⟨p, hp⟩ : S2Punctured v hv) ⟨q, hq⟩ :=
    S2Punctured.liftPath hv hp hq
      (stereographicStraightLine hv p q hp hq)
      (stereographicStraightLine_apply_mem_source hv hp hq) with hδ'_def
  -- Simple-connectedness ⇒ γ' homotopic to δ'.
  have h_homotopic : γ'.Homotopic δ' :=
    SimplyConnectedSpace.paths_homotopic γ' δ'
  -- Map through the inclusion `S2Punctured.incl`.
  have h_map :
      (γ'.map (S2Punctured.incl hv).continuous).Homotopic
        (δ'.map (S2Punctured.incl hv).continuous) :=
    h_homotopic.map (S2Punctured.incl hv)
  -- Identify the lifted/mapped paths with the originals.
  have h_γ_lhs : γ'.map (S2Punctured.incl hv).continuous = γ :=
    S2Punctured.liftPath_map_incl_eq hv hp hq γ h_image
  have h_δ_rhs : δ'.map (S2Punctured.incl hv).continuous =
      stereographicStraightLine hv p q hp hq :=
    S2Punctured.liftPath_map_incl_eq hv hp hq
      (stereographicStraightLine hv p q hp hq)
      (stereographicStraightLine_apply_mem_source hv hp hq)
  rw [h_γ_lhs, h_δ_rhs] at h_map
  exact h_map

end JacobianChallenge

end
