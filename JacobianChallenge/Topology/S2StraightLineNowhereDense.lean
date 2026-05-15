/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2StereographicStraightLine
import JacobianChallenge.Topology.S2SegmentEmptyInterior

/-! # `stereographicStraightLine` has empty interior in `sphere 0 1`

Transports chip 4g's empty-interior result from `(ℝ ∙ v)ᗮ` to
`sphere 0 1` along the stereographic projection.

Strategy: working at the `sphere 0 1` level (no subtype unfolding),
contradiction proof:

1. Suppose `interior (range stereographicStraightLine) ≠ ∅`.
2. Pick an interior point `x`. It comes with an open neighborhood
   `N` in `sphere 0 1` contained in `range`. Hence `N ⊆ source`
   (chip 4f's `stereographicStraightLine_range_subset_source`).
3. Apply `stereographic hv` to `N`. Continuity on the open source +
   bijection on source/target gives an open subset of `(ℝ ∙ v)ᗮ`
   (target = univ) contained in `stereographic hv '' range = segment`.
4. Hence interior of segment is nonempty, contradicting chip 4g.

This avoids the `S2Punctured` subtype machinery entirely.

## What is proved

* `interior_range_stereographicStraightLine_eq_empty` —
  `interior (Set.range (stereographicStraightLine hv p q hp hq)) = ∅`
  in `sphere 0 1`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
variable {p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
variable (hp : p ∈ (stereographic hv).source)
variable (hq : q ∈ (stereographic hv).source)

/-- `stereographic hv` applied to `stereographicStraightLine hv p q hp hq t`
recovers the line-segment-parameter point in `(ℝ ∙ v)ᗮ`. -/
private theorem stereographic_apply_stereographicStraightLine
    (t : unitInterval) :
    (stereographic hv) (stereographicStraightLine hv p q hp hq t) =
      (1 - (t : ℝ)) • (stereographic hv p) + (t : ℝ) • (stereographic hv q) := by
  -- `stereographicStraightLine` is defined as
  -- `(stereographic hv).symm` of the linear interpolation, and
  -- `(stereographic hv).right_inv` is identity on its target = univ.
  show (stereographic hv)
      ((stereographic hv).symm ((1 - (t : ℝ)) • (stereographic hv p) +
        (t : ℝ) • (stereographic hv q))) = _
  apply (stereographic hv).right_inv
  rw [stereographic_target hv]
  exact Set.mem_univ _

/-- The image of the path's range under `stereographic hv` is exactly
the line segment between the stereographic projections of the endpoints. -/
theorem stereographic_image_range_eq_segment :
    (stereographic hv) '' (Set.range (stereographicStraightLine hv p q hp hq)) =
      segment ℝ ((stereographic hv) p) ((stereographic hv) q) := by
  rw [segment_eq_image ℝ]
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨(t : ℝ), ⟨t.2.1, t.2.2⟩, ?_⟩
    exact (stereographic_apply_stereographicStraightLine hv hp hq t).symm
  · rintro ⟨θ, ⟨hθ_lo, hθ_hi⟩, hθ_eq⟩
    refine ⟨stereographicStraightLine hv p q hp hq ⟨θ, hθ_lo, hθ_hi⟩, ⟨_, rfl⟩, ?_⟩
    rw [stereographic_apply_stereographicStraightLine hv hp hq ⟨θ, hθ_lo, hθ_hi⟩]
    exact hθ_eq

/-- `(stereographic hv)` restricted to its source is an open map onto its
target `= univ ⊂ (ℝ ∙ v)ᗮ`. -/
private theorem stereographic_isOpenMap_on_source :
    IsOpenMap (fun p : (stereographic hv).source =>
      (stereographic hv) (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  -- This is the underlying function of `S2Punctured.equivStereographicSource ∘ ...`,
  -- which is part of `S2Punctured.stereographicHomeomorph` from chip 2.
  -- Easiest: the homeomorphism's `toFun` is a continuous bijection between
  -- the open `source` (as a subtype) and `(ℝ ∙ v)ᗮ`, hence an open map.
  have h_homeo := (S2Punctured.stereographicHomeomorph hv).isOpenMap
  exact h_homeo

/-- **Range of `stereographicStraightLine` has empty interior in `sphere 0 1`.**
By contradiction: if some open neighborhood `N ⊂ sphere 0 1` is inside
the range, then `N ⊂ source` (chip 4f); pushing forward through
`stereographic hv` gives an open subset of `(ℝ ∙ v)ᗮ` inside the
line segment, contradicting chip 4g. -/
theorem interior_range_stereographicStraightLine_eq_empty :
    interior (Set.range (stereographicStraightLine hv p q hp hq)) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  rw [mem_interior] at hx
  obtain ⟨N, hN_sub_range, hN_open, hxN⟩ := hx
  -- N ⊂ source via chip 4f.
  have hN_sub_source : N ⊆ (stereographic hv).source :=
    hN_sub_range.trans (stereographicStraightLine_range_subset_source hv hp hq)
  -- Lift N to the source subtype.
  set N_lifted : Set ((stereographic hv).source) :=
    { p : (stereographic hv).source | (p : sphere _ _) ∈ N } with hN_lifted_def
  have hN_lifted_open : IsOpen N_lifted :=
    hN_open.preimage continuous_subtype_val
  -- Push forward via the homeomorphism source ≃ₜ (ℝ ∙ v)ᗮ from chip 2.
  set f : (stereographic hv).source → ((ℝ ∙ v)ᗮ : Submodule ℝ _) :=
    fun p => S2Punctured.stereographicHomeomorph hv p with hf_def
  have hf_image_open : IsOpen (f '' N_lifted) :=
    (S2Punctured.stereographicHomeomorph hv).isOpenMap _ hN_lifted_open
  -- f '' N_lifted is nonempty (contains f ⟨x, _⟩).
  have hx_in_source : x ∈ (stereographic hv).source := hN_sub_source hxN
  have hf_image_nonempty : (f '' N_lifted).Nonempty :=
    ⟨f ⟨x, hx_in_source⟩, ⟨x, hx_in_source⟩, hxN, rfl⟩
  -- f '' N_lifted ⊆ segment.
  have hf_image_sub_seg : f '' N_lifted ⊆
      segment ℝ ((stereographic hv) p) ((stereographic hv) q) := by
    rintro _ ⟨p', hp'N, rfl⟩
    have hp'_in_range : (p' : sphere _ _) ∈
        Set.range (stereographicStraightLine hv p q hp hq) :=
      hN_sub_range hp'N
    have : f p' = (stereographic hv) (p' : sphere _ _) := rfl
    rw [this, ← stereographic_image_range_eq_segment hv hp hq]
    exact Set.mem_image_of_mem _ hp'_in_range
  -- Hence segment has nonempty interior, contradicting chip 4g.
  have h_seg_interior_nonempty :
      (interior (segment ℝ ((stereographic hv) p) ((stereographic hv) q))).Nonempty := by
    obtain ⟨y, hy⟩ := hf_image_nonempty
    refine ⟨y, mem_interior.mpr ⟨f '' N_lifted, hf_image_sub_seg, hf_image_open, hy⟩⟩
  have h_seg_interior_empty :
      interior (segment ℝ ((stereographic hv) p) ((stereographic hv) q)) = ∅ :=
    interior_segment_in_orthogonalComplement_v_eq_empty hv _ _
  rw [h_seg_interior_empty] at h_seg_interior_nonempty
  exact h_seg_interior_nonempty.ne_empty rfl

end JacobianChallenge

end
