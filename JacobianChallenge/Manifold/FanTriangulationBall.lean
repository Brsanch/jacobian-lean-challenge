/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartStraightLinePathBall
import JacobianChallenge.Manifold.Smooth2ChainStokesBoundary

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Fan-triangulation of a polygonal loop in a chart-image-ball

Ball-data analog of `FanTriangulation.lean`. Given:

* `q : X` — base point.
* `z_c_ball : ℂ`, `r : ℝ`, `hr : 0 < r`,
  `hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target` — chart-image ball.
* `z_c : ℂ` (fan apex) with `h_zc : z_c ∈ Metric.ball z_c_ball r`.
* `zs : List ℂ` with `h_ball : ∀ z ∈ zs, z ∈ Metric.ball z_c_ball r`.

The fan triangulation produces a `Smooth2Chain (𝓘(ℝ, ℂ)) X` whose
boundary equals the polygonal-edge chain plus a spoke-residue that
vanishes for closed polygons.

The induction structure of `FanTriangulation.boundary₂_fanChain`
translates here, routed through `chartStraightLinePath_ball`
(canonical, definitionally shared between adjacent fan triangles
under Lean 4 proof irrelevance).

## What this file ships

* `fanSpokesPair_ball` — the two spoke-paths for one triangle.
* `fanChain_ball`, `polygonalChain_ball`, `spokeResidue_ball` —
  the three list-indexed chains (taking `List ℂ` + a ball-membership
  hypothesis).
* `affineChartTriangleSimplex_ball_boundary_as_loop_plus_spokes`.
* `boundary₂_fanChain_ball` — the headline induction.
* `polygonalChain_ball_eq_boundary_of_closed`,
  `polygonalChain_ball_mem_smoothCycle_of_closed`,
  `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Fan spokes pair -/

/-- The "fan spokes" pair for one ball-triangle: `-single(z_c→z_j) + single(z_c→z_i)`. -/
noncomputable def fanSpokesPair_ball
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z_i z_j : ℂ)
    (h_i : z_i ∈ Metric.ball z_c_ball r)
    (h_j : z_j ∈ Metric.ball z_c_ball r) :
    SmoothChain (𝓘(ℝ, ℂ)) X :=
  -SmoothChain.single (chartStraightLinePath_ball q z_c_ball r hr hB z_c z_j h_zc h_j)
    + SmoothChain.single (chartStraightLinePath_ball q z_c_ball r hr hB z_c z_i h_zc h_i)

/-- **One ball-triangle's boundary = single(z_i → z_j) + fanSpokesPair_ball.** -/
theorem affineChartTriangleSimplex_ball_boundary_as_loop_plus_spokes
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z_i z_j : ℂ)
    (h_i : z_i ∈ Metric.ball z_c_ball r)
    (h_j : z_j ∈ Metric.ball z_c_ball r) :
    Smooth2Simplex.boundary
        (affineChartTriangleSimplex_ball q z_c_ball r hr hB z_c z_i z_j h_zc h_i h_j)
      = SmoothChain.single
          (chartStraightLinePath_ball q z_c_ball r hr hB z_i z_j h_i h_j)
        + fanSpokesPair_ball q z_c_ball r hr hB z_c h_zc z_i z_j h_i h_j := by
  rw [affineChartTriangleSimplex_ball_boundary]
  unfold fanSpokesPair_ball
  abel

@[simp] lemma fanSpokesPair_ball_degenerate
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z : ℂ) (h_z : z ∈ Metric.ball z_c_ball r) :
    fanSpokesPair_ball q z_c_ball r hr hB z_c h_zc z z h_z h_z = 0 := by
  unfold fanSpokesPair_ball
  abel

/-! ## Helpers for extracting ball-membership from a list hypothesis -/

private lemma head_mem_of_forall_mem {z_c_ball : ℂ} {r : ℝ}
    {z_i : ℂ} {rest : List ℂ}
    (h : ∀ z ∈ z_i :: rest, z ∈ Metric.ball z_c_ball r) :
    z_i ∈ Metric.ball z_c_ball r := h z_i List.mem_cons_self

private lemma second_mem_of_forall_mem {z_c_ball : ℂ} {r : ℝ}
    {z_i z_j : ℂ} {rest : List ℂ}
    (h : ∀ z ∈ z_i :: z_j :: rest, z ∈ Metric.ball z_c_ball r) :
    z_j ∈ Metric.ball z_c_ball r :=
  h z_j (List.mem_cons_of_mem _ List.mem_cons_self)

private lemma tail_forall_mem {z_c_ball : ℂ} {r : ℝ}
    {z_i : ℂ} {rest : List ℂ}
    (h : ∀ z ∈ z_i :: rest, z ∈ Metric.ball z_c_ball r) :
    ∀ z ∈ rest, z ∈ Metric.ball z_c_ball r :=
  fun z hz => h z (List.mem_cons_of_mem _ hz)

private lemma getLast_mem_of_forall_mem {z_c_ball : ℂ} {r : ℝ}
    {z_0 : ℂ} {rest : List ℂ}
    (h : ∀ z ∈ z_0 :: rest, z ∈ Metric.ball z_c_ball r) :
    (z_0 :: rest).getLast (by simp) ∈ Metric.ball z_c_ball r :=
  h _ (List.getLast_mem (by simp))

/-- Value-congruence for `chartStraightLinePath_ball`: paths with equal
endpoints are equal (the membership proofs are in `Prop`, so proof
irrelevance handles the dependent arguments). -/
private lemma chartStraightLinePath_ball_congr_tgt
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    {z₀ z₁ z₁' : ℂ} (heq : z₁ = z₁')
    (h₀ : z₀ ∈ Metric.ball z_c_ball r)
    (h₁ : z₁ ∈ Metric.ball z_c_ball r)
    (h₁' : z₁' ∈ Metric.ball z_c_ball r) :
    chartStraightLinePath_ball q z_c_ball r hr hB z₀ z₁ h₀ h₁
      = chartStraightLinePath_ball q z_c_ball r hr hB z₀ z₁' h₀ h₁' := by
  cases heq
  rfl

/-! ## Fan 2-chain, polygonal chain, spoke residue -/

/-- Fan 2-chain over consecutive pairs of `zs`, with all polygonal
vertices in `Metric.ball z_c_ball r` (by `h_ball`). -/
noncomputable def fanChain_ball
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r) :
    (zs : List ℂ) → (h_ball : ∀ z ∈ zs, z ∈ Metric.ball z_c_ball r) →
    Smooth2Chain (𝓘(ℝ, ℂ)) X
  | [], _ => 0
  | [_], _ => 0
  | z_i :: z_j :: rest, h_ball =>
    Smooth2Chain.single
        (affineChartTriangleSimplex_ball q z_c_ball r hr hB z_c z_i z_j h_zc
          (head_mem_of_forall_mem h_ball)
          (second_mem_of_forall_mem h_ball))
      + fanChain_ball q z_c_ball r hr hB z_c h_zc (z_j :: rest)
          (tail_forall_mem h_ball)

/-- Polygonal-edge chain over consecutive pairs of `zs`. -/
noncomputable def polygonalChain_ball
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target) :
    (zs : List ℂ) → (h_ball : ∀ z ∈ zs, z ∈ Metric.ball z_c_ball r) →
    SmoothChain (𝓘(ℝ, ℂ)) X
  | [], _ => 0
  | [_], _ => 0
  | z_i :: z_j :: rest, h_ball =>
    SmoothChain.single
        (chartStraightLinePath_ball q z_c_ball r hr hB z_i z_j
          (head_mem_of_forall_mem h_ball)
          (second_mem_of_forall_mem h_ball))
      + polygonalChain_ball q z_c_ball r hr hB (z_j :: rest)
          (tail_forall_mem h_ball)

/-- Spoke residue: `-single(z_c→last) + single(z_c→head)`, or `0` on
empty/singleton list. -/
noncomputable def spokeResidue_ball
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r) :
    (zs : List ℂ) → (h_ball : ∀ z ∈ zs, z ∈ Metric.ball z_c_ball r) →
    SmoothChain (𝓘(ℝ, ℂ)) X
  | [], _ => 0
  | [_], _ => 0
  | z_0 :: z_1 :: rest, h_ball =>
    -SmoothChain.single
        (chartStraightLinePath_ball q z_c_ball r hr hB z_c
          ((z_0 :: z_1 :: rest).getLast (by simp))
          h_zc
          (getLast_mem_of_forall_mem h_ball))
      + SmoothChain.single
          (chartStraightLinePath_ball q z_c_ball r hr hB z_c z_0 h_zc
            (head_mem_of_forall_mem h_ball))

/-! ## Inductive boundary identity for the fan chain -/

/-- **Inductive identity**: the boundary of `fanChain_ball z_c zs` (as a
SmoothChain) equals `polygonalChain_ball zs + spokeResidue_ball z_c zs`. -/
theorem boundary₂_fanChain_ball
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (zs : List ℂ) (h_ball : ∀ z ∈ zs, z ∈ Metric.ball z_c_ball r) :
    Smooth2Chain.boundary₂ (fanChain_ball q z_c_ball r hr hB z_c h_zc zs h_ball)
      = polygonalChain_ball q z_c_ball r hr hB zs h_ball
        + spokeResidue_ball q z_c_ball r hr hB z_c h_zc zs h_ball := by
  induction zs with
  | nil => simp [fanChain_ball, polygonalChain_ball, spokeResidue_ball]
  | cons z_0 rest ih =>
    -- `cases rest` would fail to update the dependent `h_ball` type;
    -- revert it, do the case split, then re-intro inside each branch.
    revert h_ball ih
    cases h_rest : rest with
    | nil =>
      intro _ih h_ball
      simp [fanChain_ball, polygonalChain_ball, spokeResidue_ball]
    | cons z_1 rest' =>
      intro ih h_ball
      subst h_rest
      show Smooth2Chain.boundary₂
            (Smooth2Chain.single
              (affineChartTriangleSimplex_ball q z_c_ball r hr hB z_c z_0 z_1 h_zc
                (head_mem_of_forall_mem h_ball)
                (second_mem_of_forall_mem h_ball))
              + fanChain_ball q z_c_ball r hr hB z_c h_zc (z_1 :: rest')
                  (tail_forall_mem h_ball))
          = polygonalChain_ball q z_c_ball r hr hB (z_0 :: z_1 :: rest') h_ball
            + spokeResidue_ball q z_c_ball r hr hB z_c h_zc (z_0 :: z_1 :: rest') h_ball
      rw [Smooth2Chain.boundary₂_add, Smooth2Chain.boundary₂_single]
      rw [affineChartTriangleSimplex_ball_boundary_as_loop_plus_spokes]
      rw [ih (tail_forall_mem h_ball)]
      have h_poly :
          polygonalChain_ball q z_c_ball r hr hB (z_0 :: z_1 :: rest') h_ball
            = SmoothChain.single
                (chartStraightLinePath_ball q z_c_ball r hr hB z_0 z_1
                  (head_mem_of_forall_mem h_ball)
                  (second_mem_of_forall_mem h_ball))
              + polygonalChain_ball q z_c_ball r hr hB (z_1 :: rest')
                  (tail_forall_mem h_ball) := rfl
      rw [h_poly]
      clear h_poly
      revert h_ball ih
      cases h' : rest' with
      | nil =>
        intro _ih h_ball
        unfold fanSpokesPair_ball
        simp only [polygonalChain_ball, spokeResidue_ball, add_zero]
        -- The spokeResidue_ball [z_0, z_1] term still contains `[z_0, z_1].getLast`;
        -- replace it by `z_1` via path-congruence (proof-irrelevant in membership).
        have h_last : ([z_0, z_1]).getLast (by simp) = z_1 := by
          simp [List.getLast_cons]
        have h_paths_eq :
            chartStraightLinePath_ball q z_c_ball r hr hB z_c
              (([z_0, z_1]).getLast (by simp)) h_zc
              (getLast_mem_of_forall_mem h_ball)
            = chartStraightLinePath_ball q z_c_ball r hr hB z_c z_1 h_zc
              (second_mem_of_forall_mem h_ball) :=
          chartStraightLinePath_ball_congr_tgt q z_c_ball r hr hB h_last h_zc _ _
        rw [h_paths_eq]
      | cons z_2 rest'' =>
        intro _ih h_ball
        subst h'
        unfold fanSpokesPair_ball
        -- Unfold the two `spokeResidue_ball` terms via their third pattern.
        simp only [spokeResidue_ball]
        -- The two `getLast` arguments are equal: `(z_0 :: z_1 :: z_2 :: rest'').getLast`
        -- and `(z_1 :: z_2 :: rest'').getLast` both reduce to the same tail-end.
        -- After rewriting one via a path-congruence (proof-irrelevant in the
        -- membership argument), the abel-cancellation closes the spoke pairing.
        have h_last_eq : (z_0 :: z_1 :: z_2 :: rest'').getLast (by simp)
                       = (z_1 :: z_2 :: rest'').getLast (by simp) := by
          simp [List.getLast_cons]
        have h_paths_eq :
            chartStraightLinePath_ball q z_c_ball r hr hB z_c
              ((z_0 :: z_1 :: z_2 :: rest'').getLast (by simp)) h_zc
              (getLast_mem_of_forall_mem h_ball)
            = chartStraightLinePath_ball q z_c_ball r hr hB z_c
              ((z_1 :: z_2 :: rest'').getLast (by simp)) h_zc
              (getLast_mem_of_forall_mem (tail_forall_mem h_ball)) :=
          chartStraightLinePath_ball_congr_tgt q z_c_ball r hr hB h_last_eq h_zc _ _
        rw [h_paths_eq]
        abel

/-! ## Closed-loop corollaries -/

/-- For a closed 2+-element ball-vertex list (`head = last`), the
spoke residue is zero. -/
lemma spokeResidue_ball_eq_zero_of_closed
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z_0 : ℂ) (rest : List ℂ)
    (h_ball : ∀ z ∈ z_0 :: rest, z ∈ Metric.ball z_c_ball r)
    (h_closed : (z_0 :: rest).getLast (by simp) = z_0) :
    spokeResidue_ball q z_c_ball r hr hB z_c h_zc (z_0 :: rest) h_ball = 0 := by
  cases rest with
  | nil => simp [spokeResidue_ball]
  | cons z_1 rest' =>
    show -SmoothChain.single
            (chartStraightLinePath_ball q z_c_ball r hr hB z_c
              ((z_0 :: z_1 :: rest').getLast (by simp)) h_zc
              (getLast_mem_of_forall_mem h_ball))
          + SmoothChain.single
            (chartStraightLinePath_ball q z_c_ball r hr hB z_c z_0 h_zc
              (head_mem_of_forall_mem h_ball))
        = 0
    have h_paths_eq :
        chartStraightLinePath_ball q z_c_ball r hr hB z_c
            ((z_0 :: z_1 :: rest').getLast (by simp)) h_zc
            (getLast_mem_of_forall_mem h_ball)
          = chartStraightLinePath_ball q z_c_ball r hr hB z_c z_0 h_zc
            (head_mem_of_forall_mem h_ball) :=
      chartStraightLinePath_ball_congr_tgt q z_c_ball r hr hB h_closed h_zc _ _
    rw [h_paths_eq]
    abel

/-- **Closed polygonal-loop boundary identity.** For a closed
ball-vertex list (`head = last`), the polygonal-edge chain *is* the
boundary of the fan 2-chain. -/
theorem polygonalChain_ball_eq_boundary_of_closed
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z_0 : ℂ) (rest : List ℂ)
    (h_ball : ∀ z ∈ z_0 :: rest, z ∈ Metric.ball z_c_ball r)
    (h_closed : (z_0 :: rest).getLast (by simp) = z_0) :
    polygonalChain_ball q z_c_ball r hr hB (z_0 :: rest) h_ball
      = Smooth2Chain.boundary₂
          (fanChain_ball q z_c_ball r hr hB z_c h_zc (z_0 :: rest) h_ball) := by
  rw [boundary₂_fanChain_ball]
  rw [spokeResidue_ball_eq_zero_of_closed q z_c_ball r hr hB z_c h_zc z_0 rest
        h_ball h_closed]
  abel

/-- **Closed polygonal-loop chain is a `SmoothCycle`.** -/
lemma polygonalChain_ball_mem_smoothCycle_of_closed
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z_0 : ℂ) (rest : List ℂ)
    (h_ball : ∀ z ∈ z_0 :: rest, z ∈ Metric.ball z_c_ball r)
    (h_closed : (z_0 :: rest).getLast (by simp) = z_0) :
    polygonalChain_ball q z_c_ball r hr hB (z_0 :: rest) h_ball
      ∈ SmoothCycle (𝓘(ℝ, ℂ)) X := by
  rw [polygonalChain_ball_eq_boundary_of_closed q z_c_ball r hr hB z_c h_zc
        z_0 rest h_ball h_closed]
  exact Smooth2Chain.boundary₂_mem_smoothCycle _

/-- **Closed polygonal chain (packaged as a SmoothCycle) lies in
`stokesBoundaries`.** Headline corollary of the chart-image-in-ball
fan-triangulation arc, valid on arbitrary compact connected complex
1-manifolds. -/
theorem polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed
    (q : X) (z_c_ball : ℂ) (r : ℝ) (hr : 0 < r)
    (hB : Metric.ball z_c_ball r ⊆ (chartAt ℂ q).target)
    (z_c : ℂ) (h_zc : z_c ∈ Metric.ball z_c_ball r)
    (z_0 : ℂ) (rest : List ℂ)
    (h_ball : ∀ z ∈ z_0 :: rest, z ∈ Metric.ball z_c_ball r)
    (h_closed : (z_0 :: rest).getLast (by simp) = z_0) :
    (⟨polygonalChain_ball q z_c_ball r hr hB (z_0 :: rest) h_ball,
        polygonalChain_ball_mem_smoothCycle_of_closed q z_c_ball r hr hB
          z_c h_zc z_0 rest h_ball h_closed⟩
          : SmoothCycle (𝓘(ℝ, ℂ)) X)
      ∈ stokesBoundaries (𝓘(ℝ, ℂ)) X := by
  refine (mem_stokesBoundaries_iff (I := 𝓘(ℝ, ℂ)) (X := X)).mpr ?_
  refine ⟨fanChain_ball q z_c_ball r hr hB z_c h_zc (z_0 :: rest) h_ball, ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (fanChain_ball q z_c_ball r hr hB z_c h_zc (z_0 :: rest) h_ball)
          : SmoothChain (𝓘(ℝ, ℂ)) X)
      = polygonalChain_ball q z_c_ball r hr hB (z_0 :: rest) h_ball
  rw [Smooth2Chain.boundary₂Cycle_coe]
  exact (polygonalChain_ball_eq_boundary_of_closed q z_c_ball r hr hB z_c h_zc
          z_0 rest h_ball h_closed).symm

end JacobianChallenge

end
