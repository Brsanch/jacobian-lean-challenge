/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2EquatorialBeltPathConnected
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Combination

/-! # Line segments in `(ℝ ∙ v)ᗮ` have empty interior

The dimensional ingredient for the polygonal-approximation argument:
in a real vector space of finite dimension `2` (such as the orthogonal
complement of a unit vector in `EuclideanSpace ℝ (Fin 3)`), the line
segment between any two points has empty interior. Its image under
the stereographic homeomorphism is therefore nowhere dense in
`(stereographic hv).source ⊂ S²`.

This is the missing piece for closing
`EveryS2LoopHomotopicToNonSurjective`: a polygonal `γ'`'s image is
a finite union of stereographic line-segment images, each
nowhere-dense; the Baire union argument concludes `range γ' ≠ univ`.

## Strategy

* `convexHull_pair : convexHull ℝ {a, b} = segment ℝ a b` (mathlib).
* `interior_convexHull_nonempty_iff_affineSpan_eq_top` (mathlib) —
  interior nonempty iff `affineSpan ℝ {a, b} = ⊤`.
* `direction_affineSpan` + `vectorSpan_pair` —
  `(affineSpan ℝ {a, b}).direction = ℝ ∙ (a -ᵥ b)`, rank ≤ 1.
* `(ℝ ∙ v)ᗮ` has rank `2` (chip 4d's
  `finrank_orthogonalComplement_v_eq_two`); rank-1 strict-subset of
  rank-2 cannot be top, contradiction.

## What is proved

* `interior_segment_in_orthogonalComplement_v_eq_empty` —
  `interior (segment ℝ a b) = ∅` for any `a b ∈ (ℝ ∙ v)ᗮ` with
  `‖v‖ = 1` in `EuclideanSpace ℝ (Fin 3)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

/-- **Segment interior empty in 2D.** For any two points `a, b` in the
2-dimensional orthogonal complement `(ℝ ∙ v)ᗮ ⊂ EuclideanSpace ℝ (Fin 3)`,
the line segment from `a` to `b` has empty interior.

Proof outline:

1. By contradiction, suppose `interior (segment ℝ a b) ≠ ∅`.
2. `segment ℝ a b = convexHull ℝ {a, b}` (mathlib `convexHull_pair`).
3. `interior_convexHull_nonempty_iff_affineSpan_eq_top` gives
   `affineSpan ℝ ({a, b} : Set _) = ⊤`.
4. The direction of the affine span equals `vectorSpan ℝ {a, b} = ℝ ∙ (a -ᵥ b)`
   (rank ≤ 1).
5. But the direction of `⊤` equals `⊤`, which has rank `2` in `(ℝ ∙ v)ᗮ`
   (chip 4d's `finrank_orthogonalComplement_v_eq_two`).
6. `1 ≥ 2`, contradiction. -/
theorem interior_segment_in_orthogonalComplement_v_eq_empty
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    (a b : ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) :
    interior (segment ℝ a b) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  intro h_nonempty
  haveI : FiniteDimensional ℝ
      ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :=
    FiniteDimensional.of_finrank_eq_succ
      (n := 1) (finrank_orthogonalComplement_v_eq_two hv)
  -- segment = convexHull {a, b}.
  rw [show segment ℝ a b = convexHull ℝ {a, b} from (convexHull_pair a b).symm]
      at h_nonempty
  -- interior nonempty ⇒ affineSpan = ⊤.
  have h_aff_top : affineSpan ℝ ({a, b} : Set _) = ⊤ :=
    (interior_convexHull_nonempty_iff_affineSpan_eq_top).mp h_nonempty
  -- direction of the affine span equals the vectorSpan, which equals ℝ ∙ (a - b).
  have h_dir_eq : (affineSpan ℝ ({a, b} : Set _)).direction
      = (ℝ ∙ (a -ᵥ b) : Submodule ℝ _) := by
    rw [direction_affineSpan, vectorSpan_pair]
  -- The direction of `⊤` is `⊤`.
  have h_top_dir : (⊤ : AffineSubspace ℝ
      ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))).direction = ⊤ :=
    AffineSubspace.direction_top _ _ _
  rw [h_aff_top, h_top_dir] at h_dir_eq
  -- So `⊤ = ℝ ∙ (a -ᵥ b)`, finrank both sides.
  have h_top_finrank : Module.finrank ℝ
      (⊤ : Submodule ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ _)) =
      Module.finrank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ _) :=
    finrank_top _ _
  have h_span_finrank :
      Module.finrank ℝ ((ℝ ∙ (a -ᵥ b)) : Submodule ℝ _) ≤ 1 := by
    by_cases hab : a -ᵥ b = 0
    · rw [hab, Submodule.span_zero_singleton]; simp
    · exact (finrank_span_singleton hab).le
  have h_finrank_top_val : Module.finrank ℝ
      ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) = 2 :=
    finrank_orthogonalComplement_v_eq_two hv
  have h_eq_finrank : Module.finrank ℝ
      (⊤ : Submodule ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ _)) =
      Module.finrank ℝ ((ℝ ∙ (a -ᵥ b)) : Submodule ℝ _) := by
    rw [h_dir_eq]
  rw [h_top_finrank, h_finrank_top_val] at h_eq_finrank
  -- h_eq_finrank : 2 = Module.finrank ℝ ((ℝ ∙ (a -ᵥ b)) ...).
  -- h_span_finrank : ... ≤ 1.
  -- 2 ≤ 1, contradiction.
  omega

end JacobianChallenge

end
