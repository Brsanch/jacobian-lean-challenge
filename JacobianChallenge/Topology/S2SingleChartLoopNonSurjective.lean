/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2StraightLineNowhereDense

/-! # Loops contained in a single stereographic chart are homotopic to non-surjective loops

A self-contained corollary of chips 4f + 4h: any path in `sphere 0 1`
whose image lies in a single stereographic chart's source is
`Path.Homotopic` to a `stereographicStraightLine`, whose range has
empty interior in `sphere 0 1` (chip 4h) and hence is not all of
`sphere 0 1`.

This is a per-segment building block for the final polygonal-
approximation closure of `EveryS2LoopHomotopicToNonSurjective`.

## What is proved

* `singleChart_path_homotopic_nonSurjective` — for any
  `γ : Path x y` in `sphere 0 1` with `γ` entirely inside
  `(stereographic hv).source`, there exists `γ' : Path x y` such
  that `γ ≃ γ'` and `range γ' ≠ univ`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
variable {x y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}

/-- **Single-chart non-surjective replacement.** If a path
`γ : Path x y` has all its values in `(stereographic hv).source`,
then it is `Path.Homotopic` to a `stereographicStraightLine` whose
range — being the stereographic preimage of a 1-dimensional segment
in a 2-dimensional Euclidean space — has empty interior in
`sphere 0 1` and is therefore not equal to `univ`. -/
theorem singleChart_path_homotopic_nonSurjective
    (γ : Path x y)
    (h_image : ∀ t : unitInterval, γ t ∈ (stereographic hv).source) :
    ∃ γ' : Path x y, γ.Homotopic γ' ∧ Set.range γ' ≠ (Set.univ : Set _) := by
  have hx : x ∈ (stereographic hv).source := γ.source ▸ h_image 0
  have hy : y ∈ (stereographic hv).source := γ.target ▸ h_image 1
  refine ⟨stereographicStraightLine hv x y hx hy, ?_, ?_⟩
  · exact stereographicStraightLine_homotopic hv hx hy γ h_image
  · -- range has empty interior, so can't be univ.
    intro h_range_univ
    have h_int_empty :
        interior (Set.range (stereographicStraightLine hv x y hx hy)) = ∅ :=
      interior_range_stereographicStraightLine_eq_empty hv hx hy
    rw [h_range_univ, interior_univ] at h_int_empty
    -- h_int_empty : (univ : Set (sphere 0 1)) = ∅; but the sphere is nonempty.
    have : ((⟨v, by simp [hv]⟩ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : sphere _ _) ∈
        (Set.univ : Set (sphere _ _)) := Set.mem_univ _
    rw [h_int_empty] at this
    exact this

end JacobianChallenge

end
