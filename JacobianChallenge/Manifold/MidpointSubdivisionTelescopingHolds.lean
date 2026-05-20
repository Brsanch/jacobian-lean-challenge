/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineSegmentPathComplexMidpoint
import JacobianChallenge.Manifold.MidpointSubdivisionTelescoping
import JacobianChallenge.Manifold.Smooth2SimplexBoundaryLoop

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

/-! # `MidpointSubdivisionTelescoping σ α` UNCONDITIONAL

The 4-way midpoint-subdivision telescoping hypothesis holds
unconditionally for any `Smooth2Simplex 𝓘(ℝ, ℂ) X` and any holomorphic
1-form `α`:

```
complexChainPeriod (boundary σ) α
  = ∑ i : Fin 4, complexChainPeriod
      (boundary (midpointSubdivision σ i)) α.
```

## Proof strategy

Every face of `σ` and of every sub-triangle `T_i` is an
`affineSegmentPath` along an edge of `Δ²` (vertices or midpoints).
Expand the sum into 12 terms (3 faces × 4 sub-triangles) plus the
LHS-3-faces of σ.

* **Interior edges** (3 pairs cancel by orientation): the two `face0`
  terms `T_0.face0 = σ(m01, m02)` and `T_3.face0 = σ(m02, m01)` are
  reverse-affineSegmentPaths, so their complex periods sum to `0`
  (`affineSegmentPath_complexChainPeriod_reverse`). Similarly for
  `m01-m12` (between `T_1.face1` and `T_3.face1`) and `m02-m12`
  (between `T_2.face2` and `T_3.face2`).

* **Boundary edges** (3 pairs consolidate to full σ-faces): the two
  pieces along `v0-v1` (= `T_0.face2 = σ(v0, m01)` and
  `T_1.face2 = σ(m01, v1)`) sum to `σ.face2 = σ(v0, v1)` via the
  complex-period midpoint splitting
  (`affineSegmentPath_complexChainPeriod_midpoint_split`). Similarly
  for `v0-v2` (with sign `-1`) and `v1-v2`.

After cancellation and consolidation, the sum equals
`σ.face0 - σ.face1 + σ.face2` complex periods, i.e., `complexChainPeriod
(boundary σ) α`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace Smooth2Simplex

/-! ## Face parameter ↔ lineParam identifications -/

/-- **`face0Param t = lineParam v1 v2 t`** (i.e., `[1-t, t]`). -/
lemma face0Param_eq_lineParam_v1_v2 (t : ℝ) :
    Smooth2Simplex.face0Param t = lineParam Smooth2Simplex.v1 Smooth2Simplex.v2 t := by
  unfold Smooth2Simplex.face0Param lineParam Smooth2Simplex.v1 Smooth2Simplex.v2
  ext i
  fin_cases i <;> simp

/-- **`face1Param t = lineParam v0 v2 t`** (i.e., `[0, t]`). -/
lemma face1Param_eq_lineParam_v0_v2 (t : ℝ) :
    Smooth2Simplex.face1Param t = lineParam Smooth2Simplex.v0 Smooth2Simplex.v2 t := by
  unfold Smooth2Simplex.face1Param lineParam Smooth2Simplex.v0 Smooth2Simplex.v2
  ext i
  fin_cases i <;> simp

/-- **`face2Param t = lineParam v0 v1 t`** (i.e., `[t, 0]`). -/
lemma face2Param_eq_lineParam_v0_v1 (t : ℝ) :
    Smooth2Simplex.face2Param t = lineParam Smooth2Simplex.v0 Smooth2Simplex.v1 t := by
  unfold Smooth2Simplex.face2Param lineParam Smooth2Simplex.v0 Smooth2Simplex.v1
  ext i
  fin_cases i <;> simp

/-! ## Faces of `σ` as `affineSegmentPath`s

For any `σ : Smooth2Simplex 𝓘(ℝ, ℂ) X`:
* `σ.face0 = affineSegmentPath σ v1 v2`
* `σ.face1 = affineSegmentPath σ v0 v2`
* `σ.face2 = affineSegmentPath σ v0 v1`

via `SmoothPath.ext`, using the face-param ↔ lineParam identifications. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

lemma face0_eq_affineSegmentPath (σ : Smooth2Simplex I Y) :
    σ.face0 = affineSegmentPath σ Smooth2Simplex.v1 Smooth2Simplex.v2 := by
  apply SmoothPath.ext
  · show σ.toFun Smooth2Simplex.v1 = σ.toFun Smooth2Simplex.v1; rfl
  · show σ.toFun Smooth2Simplex.v2 = σ.toFun Smooth2Simplex.v2; rfl
  · intro t
    show σ.toFun (Smooth2Simplex.face0Param t.val) =
         σ.toFun (lineParam Smooth2Simplex.v1 Smooth2Simplex.v2 t.val)
    rw [face0Param_eq_lineParam_v1_v2]

lemma face1_eq_affineSegmentPath (σ : Smooth2Simplex I Y) :
    σ.face1 = affineSegmentPath σ Smooth2Simplex.v0 Smooth2Simplex.v2 := by
  apply SmoothPath.ext
  · show σ.toFun Smooth2Simplex.v0 = σ.toFun Smooth2Simplex.v0; rfl
  · show σ.toFun Smooth2Simplex.v2 = σ.toFun Smooth2Simplex.v2; rfl
  · intro t
    show σ.toFun (Smooth2Simplex.face1Param t.val) =
         σ.toFun (lineParam Smooth2Simplex.v0 Smooth2Simplex.v2 t.val)
    rw [face1Param_eq_lineParam_v0_v2]

lemma face2_eq_affineSegmentPath (σ : Smooth2Simplex I Y) :
    σ.face2 = affineSegmentPath σ Smooth2Simplex.v0 Smooth2Simplex.v1 := by
  apply SmoothPath.ext
  · show σ.toFun Smooth2Simplex.v0 = σ.toFun Smooth2Simplex.v0; rfl
  · show σ.toFun Smooth2Simplex.v1 = σ.toFun Smooth2Simplex.v1; rfl
  · intro t
    show σ.toFun (Smooth2Simplex.face2Param t.val) =
         σ.toFun (lineParam Smooth2Simplex.v0 Smooth2Simplex.v1 t.val)
    rw [face2Param_eq_lineParam_v0_v1]

/-! ## Midpoint identifications -/

lemma midpoint01_eq_midpoint2 :
    Smooth2Simplex.midpoint01 = midpoint2 Smooth2Simplex.v0 Smooth2Simplex.v1 := by
  unfold Smooth2Simplex.midpoint01 midpoint2 Smooth2Simplex.v0 Smooth2Simplex.v1
  ext i
  fin_cases i <;> simp

lemma midpoint02_eq_midpoint2 :
    Smooth2Simplex.midpoint02 = midpoint2 Smooth2Simplex.v0 Smooth2Simplex.v2 := by
  unfold Smooth2Simplex.midpoint02 midpoint2 Smooth2Simplex.v0 Smooth2Simplex.v2
  ext i
  fin_cases i <;> simp

lemma midpoint12_eq_midpoint2 :
    Smooth2Simplex.midpoint12 = midpoint2 Smooth2Simplex.v1 Smooth2Simplex.v2 := by
  unfold Smooth2Simplex.midpoint12 midpoint2 Smooth2Simplex.v1 Smooth2Simplex.v2
  ext i
  fin_cases i <;> simp

end Smooth2Simplex

/-! ## The headline: `MidpointSubdivisionTelescoping σ α` unconditional -/

/-- **`MidpointSubdivisionTelescoping σ α` UNCONDITIONAL.**

For any `σ : Smooth2Simplex 𝓘(ℝ, ℂ) X` and any `α : HolomorphicOneForm X`:

```
complexChainPeriod (boundary σ) α
  = ∑ i : Fin 4, complexChainPeriod
      (boundary (midpointSubdivision σ i)) α.
```

The 12 boundary integrals of the 4 sub-triangles cancel pairwise on
interior edges and consolidate via midpoint splitting on boundary
edges, yielding the original boundary integral of σ. -/
theorem Smooth2Simplex.midpointSubdivisionTelescoping_holds_unconditional
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) :
    Smooth2Simplex.MidpointSubdivisionTelescoping σ α := by
  -- Notation: write `P p q` for `complexChainPeriod (single (affineSegmentPath σ p q)) α`.
  -- We need: complexChainPeriod (boundary σ) α
  --   = ∑ i, complexChainPeriod (boundary (midpointSubdivision σ i)) α.
  unfold MidpointSubdivisionTelescoping
  -- Step 1: expand the sum over Fin 4 first, then unfold each summand's boundary.
  rw [show (∑ i : Fin 4,
      complexChainPeriod
        (Smooth2Simplex.boundary (Smooth2Simplex.midpointSubdivision σ i)) α) =
      complexChainPeriod (Smooth2Simplex.boundary
          (Smooth2Simplex.midpointSubdivision σ 0)) α
      + complexChainPeriod (Smooth2Simplex.boundary
          (Smooth2Simplex.midpointSubdivision σ 1)) α
      + complexChainPeriod (Smooth2Simplex.boundary
          (Smooth2Simplex.midpointSubdivision σ 2)) α
      + complexChainPeriod (Smooth2Simplex.boundary
          (Smooth2Simplex.midpointSubdivision σ 3)) α by
    rw [Fin.sum_univ_four]]
  -- Unfold each midpointSubdivision_T_i.
  rw [Smooth2Simplex.midpointSubdivision_T0,
      Smooth2Simplex.midpointSubdivision_T1,
      Smooth2Simplex.midpointSubdivision_T2,
      Smooth2Simplex.midpointSubdivision_T3]
  -- Unfold boundary on both sides and apply face identifications.
  unfold Smooth2Simplex.boundary
  rw [face0_eq_affineSegmentPath, face1_eq_affineSegmentPath,
      face2_eq_affineSegmentPath]
  rw [Smooth2Simplex.affineReparam_face0, Smooth2Simplex.affineReparam_face1,
      Smooth2Simplex.affineReparam_face2,
      Smooth2Simplex.affineReparam_face0, Smooth2Simplex.affineReparam_face1,
      Smooth2Simplex.affineReparam_face2,
      Smooth2Simplex.affineReparam_face0, Smooth2Simplex.affineReparam_face1,
      Smooth2Simplex.affineReparam_face2,
      Smooth2Simplex.affineReparam_face0, Smooth2Simplex.affineReparam_face1,
      Smooth2Simplex.affineReparam_face2]
  -- Rewrite midpoints in terms of `midpoint2`.
  rw [Smooth2Simplex.midpoint01_eq_midpoint2,
      Smooth2Simplex.midpoint02_eq_midpoint2,
      Smooth2Simplex.midpoint12_eq_midpoint2]
  -- Split each ChainPeriod (single (a - b + c)) into add/sub via lemmas.
  simp only [complexChainPeriod_add_left, complexChainPeriod_sub_left]
  -- Now everything is in terms of `complexChainPeriod (single (affineSegmentPath σ p q)) α`.
  -- Cancel the three interior pairs and consolidate the three boundary halves.
  -- Set up shorthand abbreviations using `set`.
  set v0 := Smooth2Simplex.v0
  set v1 := Smooth2Simplex.v1
  set v2 := Smooth2Simplex.v2
  set m01 := Smooth2Simplex.midpoint2 v0 v1 with hm01
  set m02 := Smooth2Simplex.midpoint2 v0 v2 with hm02
  set m12 := Smooth2Simplex.midpoint2 v1 v2 with hm12
  -- Boundary splittings:
  have h_v0v1 := Smooth2Simplex.affineSegmentPath_complexChainPeriod_midpoint_split
                    σ v0 v1 α
  have h_v0v2 := Smooth2Simplex.affineSegmentPath_complexChainPeriod_midpoint_split
                    σ v0 v2 α
  have h_v1v2 := Smooth2Simplex.affineSegmentPath_complexChainPeriod_midpoint_split
                    σ v1 v2 α
  rw [← hm01] at h_v0v1
  rw [← hm02] at h_v0v2
  rw [← hm12] at h_v1v2
  -- Interior reversals:
  have h_m01_m02 := Smooth2Simplex.affineSegmentPath_complexChainPeriod_reverse
                      σ m01 m02 α
  have h_m01_m12 := Smooth2Simplex.affineSegmentPath_complexChainPeriod_reverse
                      σ m01 m12 α
  have h_m02_m12 := Smooth2Simplex.affineSegmentPath_complexChainPeriod_reverse
                      σ m02 m12 α
  -- Now an algebraic manipulation closes everything. The signs come from:
  --   G - L1 + L2 - L3 + L4 - L5 + L6 = 0,
  -- so the linear combination is L1 - L2 + L3 - L4 + L5 - L6 in `e`.
  linear_combination h_v0v1 - h_v0v2 + h_v1v2 - h_m01_m02 + h_m01_m12 - h_m02_m12

end JacobianChallenge

end
