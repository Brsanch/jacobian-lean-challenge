/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromSimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # `SimplyConnectedS2` reduction to the loop-null-homotopy fact

The Phase-3 named hypothesis `SimplyConnectedS2`
(= `SimplyConnectedSpace JacobianChallenge.StandardS2`, see
`Topology/S2ImpliesGenus0FromSimplyConnected.lean`) is the small
mathlib gap "π₁(S²) = 0" at the pinned commit `8e3c989…`.

At that pin, mathlib provides:

* `SimplyConnectedSpace` and `simply_connected_iff_loops_nullhomotopic`
  (`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`),
* `isPathConnected_sphere` for any sphere in a real vector space of
  dimension `> 1` (`Mathlib/Analysis/Normed/Module/Connected.lean`),
* stereographic projection as a `PartialHomeomorph`
  (`Mathlib/Geometry/Manifold/Instances/Sphere.lean`),

but it does *not* provide an instance `SimplyConnectedSpace (sphere _ _)`,
nor any of the classical routes that would discharge it (van Kampen on
`S² = (S² ∖ N) ∪ (S² ∖ S)`, simplicial / general-position approximation,
or a CW structure on `S²`).

This file performs the *path-connectedness half* of the reduction, which
is unconditional at the pin, and isolates the genuinely missing
ingredient as a single narrower named hypothesis
`S2LoopsNullHomotopic`. The combined assembly
`simplyConnectedS2_of_loops_nullhomotopic` shows that
`S2LoopsNullHomotopic` alone suffices for `SimplyConnectedS2`,
because path-connectedness comes for free from mathlib.

## What is proved

* `JacobianChallenge.StandardS2.instNonempty` — `StandardS2` is nonempty
  (witness: a unit basis vector).
* `JacobianChallenge.StandardS2.instPathConnectedSpace` — `StandardS2`
  is path-connected as a topological subspace of
  `EuclideanSpace ℝ (Fin 3)`, via `isPathConnected_sphere` and the
  rank-`3` calculation for `EuclideanSpace ℝ (Fin 3)`.

## What remains named

* `S2LoopsNullHomotopic : Prop` — for every basepoint `x : StandardS2`
  and every loop `γ : Path x x`, `γ` is `Path.Homotopic` to
  `Path.refl x`. This is the strict π₁(S²) = 0 fact, with
  path-connectedness already discharged on the side. It is strictly
  narrower than the original `SimplyConnectedS2` Prop because the
  path-connectedness conjunct has been peeled off.

## Composition lemma

* `simplyConnectedS2_of_loops_nullhomotopic` — given
  `S2LoopsNullHomotopic`, conclude `SimplyConnectedS2`. The proof is
  the `simply_connected_iff_loops_nullhomotopic.mpr` direction,
  consuming the path-connectedness instance proved above.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric

namespace JacobianChallenge

/-! ## `StandardS2` instances -/

/-- A unit basis vector in `EuclideanSpace ℝ (Fin 3)` lies on
`Metric.sphere 0 1`, so `StandardS2` is inhabited. -/
instance StandardS2.instNonempty : Nonempty JacobianChallenge.StandardS2 := by
  refine ⟨⟨EuclideanSpace.single 0 (1 : ℝ), ?_⟩⟩
  simp [mem_sphere_iff_norm]

/-- `EuclideanSpace ℝ (Fin 3)` has `ℝ`-rank strictly greater than `1`.

This is the rank hypothesis required by mathlib's
`isPathConnected_sphere` to conclude that the unit sphere is
path-connected. We prove it once here to avoid duplicating the
finrank → rank conversion downstream. -/
theorem rank_euclideanSpace_fin_three_gt_one :
    (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by norm_num : (1 : ℕ) < 3)

/-- The unit sphere in `EuclideanSpace ℝ (Fin 3)` is path-connected as a
`Set`. Direct application of mathlib's `isPathConnected_sphere` once the
rank-`> 1` hypothesis is in hand. (`StandardS2` is definitionally the
subtype of this set; the next instance lifts this to
`PathConnectedSpace`.) -/
theorem isPathConnected_unitSphere_fin_three :
    IsPathConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isPathConnected_sphere rank_euclideanSpace_fin_three_gt_one
    (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one

/-- The standard 2-sphere, viewed as a topological subspace of
`EuclideanSpace ℝ (Fin 3)`, is path-connected. -/
instance StandardS2.instPathConnectedSpace :
    PathConnectedSpace JacobianChallenge.StandardS2 :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_unitSphere_fin_three

/-! ## Narrower named hypothesis: loop-null-homotopy on `S²` -/

/-- **Strict π₁(S²) = 0 fact.** Every loop in the standard 2-sphere is
homotopic to the constant loop at its basepoint. This is the precise
remaining mathlib gap once path-connectedness is in hand; combined with
`StandardS2.instPathConnectedSpace` it discharges
`SimplyConnectedS2`.

Classical proofs at this granularity:

* **Stereographic + general-position**: for any loop `γ : Path x x`,
  pick `y ∉ image γ` (Baire / measure / smoothing). Then
  `image γ ⊆ StandardS2 ∖ {y} ≃ₜ (ℝ ∙ y)ᗮ ≃ₜ ℝ²` via mathlib's
  `stereographic`; in `ℝ²` (which is convex, hence contractible, hence
  simply connected) any loop is null-homotopic; transport back.
* **Open-cover van Kampen**: `S² = (S² ∖ N) ∪ (S² ∖ S)` with each side
  contractible and intersection path-connected; mathlib lacks
  Seifert-van Kampen at this pin.
* **CW structure**: one 0-cell + one 2-cell ⇒ π₁ = 0 by cellular
  approximation; mathlib lacks cellular approximation at this pin.

The first route is the most tractable in mathlib style and is the
recommended next chip after this reduction. -/
def S2LoopsNullHomotopic : Prop :=
  ∀ (x : JacobianChallenge.StandardS2) (γ : Path x x),
    Path.Homotopic γ (Path.refl x)

/-! ## Reduction theorem -/

/-- **`SimplyConnectedS2` from `S2LoopsNullHomotopic`.** Combines the
unconditional path-connectedness instance above with mathlib's
characterisation `simply_connected_iff_loops_nullhomotopic`. After this
reduction, the remaining Phase-3 obligation for `SimplyConnectedS2` is
exactly `S2LoopsNullHomotopic` — a strictly narrower statement than the
broad `SimplyConnectedSpace StandardS2` because the path-connectedness
conjunct has been discharged. -/
theorem simplyConnectedS2_of_loops_nullhomotopic
    (h : S2LoopsNullHomotopic) : SimplyConnectedS2 := by
  rw [SimplyConnectedS2, simply_connected_iff_loops_nullhomotopic]
  exact ⟨inferInstance, h⟩

end JacobianChallenge

end
