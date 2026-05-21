/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AdjacentTriangleCancellation

set_option linter.unusedSectionVars false

/-! # Fan-triangulation of a polygonal loop in a chart

Given a list of points `z_center, z₀, z₁, …, z_n : ℂ` (all in the chart
target of a full-target chart at `q : X`), the **fan triangulation**
consists of `n` triangles `(z_center, z_i, z_{i+1})` for `i = 0, …, n-1`.

The boundary of the resulting 2-chain, modulo stokesBoundaries, equals
the polygonal loop chain

  `single(path z₀→z₁) + single(path z₁→z₂) + … + single(path z_{n-1}→z_n)`

minus the "spokes" `path z_center→z_0` and `path z_n→z_center` (which
together close the polygonal loop into a closed cycle through z_center).

When the polygonal loop is itself closed (`z_n = z₀`) — i.e. the
"fan" is a triangulation of a closed polygon — the spokes cancel, and
the polygonal-loop chain lies in stokesBoundaries.

This file ships the **single-triangle** form for now (base case of
the fan): the boundary of one triangle `(z_center, zᵢ, zⱼ)` already
gives `single(path zᵢ→zⱼ)` modulo two spoke contributions. Generalizing
to an arbitrary fan is straightforward induction (next chip).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The "fan spokes" pair for one triangle in a fan from `z_c`. -/
noncomputable def fanSpokesPair
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z_i z_j : ℂ) :
    SmoothChain (𝓘(ℝ, ℂ)) X :=
  -SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_j)
    + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_i)

/-- **One triangle's boundary = single(z_i → z_j) + fanSpokesPair.** -/
theorem affineChartTriangleSimplex_boundary_as_loop_plus_spokes
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z_i z_j : ℂ) :
    Smooth2Simplex.boundary
        (affineChartTriangleSimplex_univ q h_univ z_c z_i z_j)
      = SmoothChain.single (chartStraightLinePath_univ q h_univ z_i z_j)
        + fanSpokesPair q h_univ z_c z_i z_j := by
  rw [affineChartTriangleSimplex_univ_boundary]
  unfold fanSpokesPair
  abel

/-- For a closed polygonal loop (start = end = `z₀`), the fan from a
single `z_c` to `(z₀, z₀)` is a *degenerate* triangle, but the
formula still produces a sensible cancellation: the two spoke
contributions `-single(z_c→z₀) + single(z_c→z₀) = 0`, leaving just
`single(z₀→z₀)`. -/
@[simp] lemma fanSpokesPair_degenerate
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z : ℂ) :
    fanSpokesPair q h_univ z_c z z = 0 := by
  unfold fanSpokesPair
  abel

/-! ## Fan 2-chain from a list of polygonal vertices

Given a center `z_c` and a list `zs : List ℂ` (consecutive pairs in
`zs` are the polygonal edges), the **fan 2-chain** is the formal sum
of triangles `(z_c, z_i, z_{i+1})` for each adjacent pair. -/

/-- The fan 2-chain over consecutive pairs of `zs`. -/
noncomputable def fanChain
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c : ℂ) :
    List ℂ → Smooth2Chain (𝓘(ℝ, ℂ)) X
  | [] => 0
  | [_] => 0
  | z_i :: z_j :: rest =>
    Smooth2Chain.single (affineChartTriangleSimplex_univ q h_univ z_c z_i z_j)
      + fanChain q h_univ z_c (z_j :: rest)

/-- The polygonal-edge chain over consecutive pairs of `zs`. -/
noncomputable def polygonalChain
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) :
    List ℂ → SmoothChain (𝓘(ℝ, ℂ)) X
  | [] => 0
  | [_] => 0
  | z_i :: z_j :: rest =>
    SmoothChain.single (chartStraightLinePath_univ q h_univ z_i z_j)
      + polygonalChain q h_univ (z_j :: rest)

@[simp] lemma fanChain_nil
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c : ℂ) :
    fanChain q h_univ z_c [] = 0 := rfl

@[simp] lemma fanChain_singleton
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z : ℂ) :
    fanChain q h_univ z_c [z] = 0 := rfl

@[simp] lemma polygonalChain_nil
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) :
    polygonalChain q h_univ [] = 0 := rfl

@[simp] lemma polygonalChain_singleton
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z : ℂ) :
    polygonalChain q h_univ [z] = 0 := rfl

/-! ## Spoke residue for a list -/

/-- The spoke residue: `single(z_c→head) - single(z_c→last)`, or `0` on empty list. -/
noncomputable def spokeResidue
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c : ℂ) :
    List ℂ → SmoothChain (𝓘(ℝ, ℂ)) X
  | [] => 0
  | [_] => 0
  | z_0 :: rest =>
    -SmoothChain.single
        (chartStraightLinePath_univ q h_univ z_c ((z_0 :: rest).getLast (by simp)))
      + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_0)

@[simp] lemma spokeResidue_nil
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c : ℂ) :
    spokeResidue q h_univ z_c [] = 0 := rfl

@[simp] lemma spokeResidue_singleton
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c z : ℂ) :
    spokeResidue q h_univ z_c [z] = 0 := rfl

/-! ## Inductive boundary identity for the fan chain -/

/-- **Inductive identity**: the boundary of `fanChain z_c zs` (as a
SmoothChain) equals `polygonalChain zs + spokeResidue z_c zs`. -/
theorem boundary₂_fanChain
    (q : X) (h_univ : (chartAt ℂ q).target = Set.univ) (z_c : ℂ)
    (zs : List ℂ) :
    Smooth2Chain.boundary₂ (fanChain q h_univ z_c zs)
      = polygonalChain q h_univ zs + spokeResidue q h_univ z_c zs := by
  induction zs with
  | nil => simp [fanChain, polygonalChain]
  | cons z_0 rest ih =>
    cases h_rest : rest with
    | nil => simp [fanChain, polygonalChain]
    | cons z_1 rest' =>
      subst h_rest
      show Smooth2Chain.boundary₂
            (Smooth2Chain.single
              (affineChartTriangleSimplex_univ q h_univ z_c z_0 z_1)
              + fanChain q h_univ z_c (z_1 :: rest'))
          = polygonalChain q h_univ (z_0 :: z_1 :: rest')
            + spokeResidue q h_univ z_c (z_0 :: z_1 :: rest')
      rw [Smooth2Chain.boundary₂_add, Smooth2Chain.boundary₂_single]
      rw [affineChartTriangleSimplex_boundary_as_loop_plus_spokes]
      rw [ih]
      have h_poly : polygonalChain q h_univ (z_0 :: z_1 :: rest')
          = SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + polygonalChain q h_univ (z_1 :: rest') := rfl
      rw [h_poly]
      -- Both spokeResidues unfold to the third pattern branch since their
      -- input lists are 2+ elements.
      cases h' : rest' with
      | nil =>
        unfold fanSpokesPair
        simp only [polygonalChain_singleton, spokeResidue_singleton, add_zero]
        show SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + (-SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_1)
              + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_0))
          = SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + spokeResidue q h_univ z_c [z_0, z_1]
        show _ = _ +
            (-SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_1)
              + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_0))
        abel
      | cons z_2 rest'' =>
        subst h'
        -- Both residues unfold (their inputs are 2+ elements lists).
        show SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + fanSpokesPair q h_univ z_c z_0 z_1
            + (polygonalChain q h_univ (z_1 :: z_2 :: rest'')
              + spokeResidue q h_univ z_c (z_1 :: z_2 :: rest''))
          = SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + polygonalChain q h_univ (z_1 :: z_2 :: rest'')
            + spokeResidue q h_univ z_c (z_0 :: z_1 :: z_2 :: rest'')
        unfold fanSpokesPair
        have h_last_eq : (z_0 :: z_1 :: z_2 :: rest'').getLast (by simp)
                      = (z_1 :: z_2 :: rest'').getLast (by simp) := by
          simp [List.getLast_cons]
        show _ = _
        show SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + (-SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_1)
              + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_0))
            + (polygonalChain q h_univ (z_1 :: z_2 :: rest'')
              + (-SmoothChain.single
                  (chartStraightLinePath_univ q h_univ z_c
                    ((z_1 :: z_2 :: rest'').getLast (by simp)))
                + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_1)))
          = SmoothChain.single (chartStraightLinePath_univ q h_univ z_0 z_1)
            + polygonalChain q h_univ (z_1 :: z_2 :: rest'')
            + (-SmoothChain.single
                (chartStraightLinePath_univ q h_univ z_c
                  ((z_0 :: z_1 :: z_2 :: rest'').getLast (by simp)))
              + SmoothChain.single (chartStraightLinePath_univ q h_univ z_c z_0))
        rw [h_last_eq]
        abel

end JacobianChallenge

end
