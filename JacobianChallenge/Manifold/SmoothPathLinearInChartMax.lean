/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathLinearInChart

set_option linter.unusedSectionVars false

/-! # Maximal-atlas variant of `SmoothPath.linearInChartSegment`

Parallel to `SmoothPath.linearInChartSegment`
(`SmoothPathLinearInChart.lean`) but parameterised by `h_max : φ ∈
IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X` instead of `h_atlas : φ ∈
atlas ℂ X`. The two functions produce the same `SmoothPath` whenever
both apply (via Prop irrelevance on the `smooth` field; src, tgt,
toPath are identical).

Motivation. The original `linearInChartSegment` parameter `h_atlas`
is consumed exactly once in its body, via
`IsManifold.subset_maximalAtlas (n := ⊤) h_atlas` to obtain
`φ ∈ maximalAtlas 𝓘(ℝ, ℂ) ⊤ X`. Taking `h_max` directly removes the
atlas-membership requirement, which is the structural obstacle to
discharging the `PathPrimitiveAdmissibleChartCover` predicate on
arbitrary compact connected complex 1-manifolds: the canonical
`chartAt ℂ x` is in `atlas` but does not have convex target, while
`convexBallChartAt x` has convex target and lies in the **maximal**
atlas, not the underlying atlas.

A downstream maximal-atlas refactor of the chartLocalPrimitive arc
will rebuild `chartLocalPrimitive`, `chartLocalPrimitiveExtend`,
`ChartLocalPrimitiveSmoothExt`, `ChartLocalPrimitiveFTC`,
`PathPrimitiveAdmissibleChartCover`, and the cover-discharge
instances on top of `linearInChartSegmentMax`. The parallel-file
approach taken here lets the existing `atlas`-based chain continue
to function unchanged, while the new maximal-atlas chain is built up
file by file.

## What this file ships

* `SmoothPath.linearInChartSegmentMax` — the maximal-atlas variant.
* `SmoothPath.linearInChartSegmentMax_src`,
  `SmoothPath.linearInChartSegmentMax_tgt` — endpoint identities.
* `SmoothPath.linearInChartSegmentMax_eq_linearInChartSegment` —
  equality of the two SmoothPath values when both apply (i.e. when
  `h_atlas` is available, the max-version with
  `subset_maximalAtlas h_atlas` produces the same `SmoothPath` as
  the original).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open Function Set

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-- **Maximal-atlas variant of `SmoothPath.linearInChartSegment`.**

Given a chart `φ` of `X` in the maximal atlas for the ℝ-`⊤`
manifold structure (provided uniformly via `complexManifoldRealification`
from `[IsManifold 𝓘(ℂ, ℂ) ω X]`), two points `p q : X` in `φ.source`,
and the hypothesis that the closed segment from `φ p` to `φ q` lies
in `φ.target`, build a `SmoothPath 𝓘(ℝ, ℂ) X` from `p` to `q`. The
ambient is `f t = φ.symm (bumpedSegment (φ p) (φ q) t)`. Identical
construction to `SmoothPath.linearInChartSegment`, with `h_atlas`
replaced by `h_max`. -/
noncomputable def SmoothPath.linearInChartSegmentMax
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_seg : segment ℝ (φ p) (φ q) ⊆ φ.target) :
    SmoothPath 𝓘(ℝ, ℂ) X where
  src := p
  tgt := q
  toPath :=
    { toFun := fun t : unitInterval =>
        φ.symm (bumpedSegment (φ p) (φ q) t.val)
      continuous_toFun := by
        have h_seg_cont : Continuous fun t : unitInterval =>
            bumpedSegment (φ p) (φ q) t.val :=
          ((contDiff_bumpedSegment (φ p) (φ q)).continuous).comp
            continuous_subtype_val
        have h_symm_cont : ContinuousOn (φ.symm : ℂ → X) φ.target :=
          φ.continuousOn_invFun
        refine h_symm_cont.comp_continuous h_seg_cont
          (fun t => h_seg (bumpedSegment_mem_segment _ _ _))
      source' := by
        show φ.symm (bumpedSegment (φ p) (φ q) (0 : unitInterval).val) = p
        have h0 : (0 : unitInterval).val = (0 : ℝ) := rfl
        rw [h0, bumpedSegment_zero]
        exact φ.left_inv hp
      target' := by
        show φ.symm (bumpedSegment (φ p) (φ q) (1 : unitInterval).val) = q
        have h1 : (1 : unitInterval).val = (1 : ℝ) := rfl
        rw [h1, bumpedSegment_one]
        exact φ.left_inv hq }
  smooth := by
    refine ⟨fun t : ℝ => φ.symm (bumpedSegment (φ p) (φ q) t), ?_, ?_⟩
    · -- Smoothness from the maximal-atlas chart-inverse smoothness.
      have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (φ.symm : ℂ → X) φ.target :=
        contMDiffOn_symm_of_mem_maximalAtlas h_max
      intro t
      have h_seg_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (bumpedSegment (φ p) (φ q)) t :=
        (contMDiff_bumpedSegment (φ p) (φ q)) t
      have h_in_target : bumpedSegment (φ p) (φ q) t ∈ φ.target :=
        h_seg (bumpedSegment_mem_segment _ _ _)
      have h_symm_at_top : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
          (φ.symm : ℂ → X) (bumpedSegment (φ p) (φ q) t) :=
        (h_symm _ h_in_target).contMDiffAt (φ.open_target.mem_nhds h_in_target)
      have h_symm_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
          (φ.symm : ℂ → X) (bumpedSegment (φ p) (φ q) t) :=
        h_symm_at_top.of_le (by decide)
      exact h_symm_at.comp t h_seg_at
    · intro t
      rfl

@[simp] lemma SmoothPath.linearInChartSegmentMax_src
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_seg : segment ℝ (φ p) (φ q) ⊆ φ.target) :
    (SmoothPath.linearInChartSegmentMax φ h_max p q hp hq h_seg).src = p := rfl

@[simp] lemma SmoothPath.linearInChartSegmentMax_tgt
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_seg : segment ℝ (φ p) (φ q) ⊆ φ.target) :
    (SmoothPath.linearInChartSegmentMax φ h_max p q hp hq h_seg).tgt = q := rfl

/-- **Identification with the atlas-parameterised original.** When the
chart `φ` is in `atlas ℂ X` (and hence in the maximal atlas via
`subset_maximalAtlas`), the two constructors produce the same
`SmoothPath`. The `src`, `tgt`, and `toPath` fields are identical by
construction; the `smooth` field is a `Prop ∃` and equal by
propositional extensionality. -/
lemma SmoothPath.linearInChartSegmentMax_eq_linearInChartSegment
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_seg : segment ℝ (φ p) (φ q) ⊆ φ.target) :
    SmoothPath.linearInChartSegmentMax φ
        (IsManifold.subset_maximalAtlas (n := ⊤) h_atlas)
        p q hp hq h_seg
      = SmoothPath.linearInChartSegment φ h_atlas p q hp hq h_seg := by
  -- Two SmoothPaths with definitionally equal src, tgt, toPath are
  -- equal by `SmoothPath` ext (the `smooth` field is a Prop).
  rfl

end JacobianChallenge

end
