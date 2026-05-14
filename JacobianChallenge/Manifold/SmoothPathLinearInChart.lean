/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.SmoothChain

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth-path-connectedness primitives 2 / 2′: `linearInChart` and `linearInChartSegment`

Builds smooth paths between two points `p q : X` lying in the source of
a common chart `φ`. Two variants are offered, distinguished by the
hypothesis on `φ.target`.

## Variant 1 (`linearInChart`): "line in target"

The original constructor produces a `SmoothPath` whose ambient
extension `f : ℝ → X` is `f t = φ.symm (affineSegment (φ p) (φ q) t)`
— the chart-coordinate **line** through `φ p, φ q` parameterised
affinely. Its globally-defined regularity is ω; we downcast to the
C^∞ regularity required by `SmoothPath.smooth` via
`ContMDiffAt.of_le`. The hypothesis is "the entire line through
`φ p, φ q` lies in `φ.target`," automatic when `φ.target = univ` (e.g.
the two charts of `RiemannSphere`).

## Variant 2 (`linearInChartSegment`): "segment in target"

The C^∞ refactor of `SmoothPath` (regularity `∞ : WithTop ℕ∞`,
*not* the analytic ω) makes a strictly weaker constructor possible:
reparameterise the affine line by `Real.smoothTransition`, a C^∞
function ℝ → [0,1] that equals 0 for `t ≤ 0` and 1 for `t ≥ 1`. The
chart-coordinate image of the resulting curve lies in the closed
segment `[φ p, φ q]` for *all* `t ∈ ℝ`, so the hypothesis weakens to
"the segment from `φ p` to `φ q` lies in `φ.target`." This is the
natural hypothesis for the chart-cover argument lifting
`linearInChartSegment` to `SmoothPathConnected I X` on a compact
connected complex 1-manifold — convex chart targets (open balls in
ℂ) discharge the segment-in-target hypothesis automatically.

The segment-in-target reparameterisation is **only available at C^∞**
because `smoothTransition` is C^∞-smooth but not real-analytic
(`expNegInvGlue`, its building block, has identically-zero germ at
0 ∈ ℝ but is positive on (0, ∞), violating the analytic identity
theorem on ℝ).

## What this file delivers

* `affineSegment a b t : ℂ` — the affine combination `(1 - t) • a + t • b`.
* `contDiff_affineSegment` — `affineSegment` is analytic in `t`.
* `affineSegment_zero` / `affineSegment_one` — endpoint identities.
* `SmoothPath.linearInChart` (line-in-target variant) and
  `linearInChart_src` / `_tgt`.
* `bumpedSegment a b t` — the reparameterised affine segment
  `(1 - σ t) • a + σ t • b` where `σ = Real.smoothTransition`.
* `bumpedSegment_zero` / `bumpedSegment_one` / `bumpedSegment_mem_segment`.
* `contDiff_bumpedSegment` — `bumpedSegment` is C^∞ on `ℝ`.
* `SmoothPath.linearInChartSegment` (segment-in-target variant) and
  `linearInChartSegment_src` / `_tgt`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Function

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-! ## Affine segment in `ℂ`, parameterised by `ℝ` -/

/-- The affine segment from `a` to `b` in `ℂ`, parameterised by
`t : ℝ`: `affineSegment a b t = (1 - t) • a + t • b`. Equals `a` at
`t = 0` and `b` at `t = 1`; analytic globally as a function `ℝ → ℂ`. -/
def affineSegment (a b : ℂ) (t : ℝ) : ℂ := (1 - t) • a + t • b

@[simp] lemma affineSegment_zero (a b : ℂ) : affineSegment a b 0 = a := by
  simp [affineSegment]

@[simp] lemma affineSegment_one (a b : ℂ) : affineSegment a b 1 = b := by
  simp [affineSegment]

/-- **The affine segment is `C^ω` (analytic) as a function `ℝ → ℂ`.**
Each term is an affine real function on `ℝ`, hence analytic; the sum
of analytic functions is analytic. Stated at the top regularity
`⊤ : WithTop ℕ∞` (= `ω` per the `ContDiff` notation scope) to feed
directly into `ContMDiff` at the ω level required by `SmoothPath`. -/
lemma contDiff_affineSegment (a b : ℂ) :
    ContDiff ℝ ⊤ (affineSegment a b) := by
  unfold affineSegment
  -- `(1 - t) • a` as a function of `t`: `(const 1 - id) • const a`.
  have h₁ : ContDiff ℝ ⊤ (fun t : ℝ => (1 - t) • a) :=
    (contDiff_const (c := (1 : ℝ))).sub contDiff_id |>.smul contDiff_const
  -- `t • b` as a function of `t`: `id • const b`.
  have h₂ : ContDiff ℝ ⊤ (fun t : ℝ => t • b) :=
    contDiff_id.smul (contDiff_const (c := b))
  exact h₁.add h₂

/-- **Manifold-side analyticity of the affine segment.** The model
on the source `ℝ` is `𝓘(ℝ, ℝ)`; the model on the target `ℂ` is
`𝓘(ℝ, ℂ)`. `contMDiff_iff_contDiff` (mathlib) translates the
`ContDiff ℝ` content of `contDiff_affineSegment` into this manifold
shape. -/
lemma contMDiff_affineSegment (a b : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ⊤ (affineSegment a b) :=
  (contDiff_affineSegment a b).contMDiff

/-! ## `SmoothPath.linearInChart` -/

/-- **Linear-in-chart smooth path.** Given a chart `φ` of `X` in
`atlas ℂ X`, two points `p q : X` in `φ.source`, and the hypothesis
that the entire line through `φ p` and `φ q` lies in `φ.target`,
build a `SmoothPath 𝓘(ℝ, ℂ) X` from `p` to `q`. The ambient is
`f t = φ.symm (affineSegment (φ p) (φ q) t)`, well-defined on all of
`ℝ` by the hypothesis. -/
noncomputable def SmoothPath.linearInChart
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_line : ∀ t : ℝ, affineSegment (φ p) (φ q) t ∈ φ.target) :
    SmoothPath 𝓘(ℝ, ℂ) X where
  src := p
  tgt := q
  toPath :=
    { toFun := fun t : unitInterval =>
        φ.symm (affineSegment (φ p) (φ q) t.val)
      continuous_toFun := by
        -- Compose: the chart-coordinate function is continuous
        -- (affine in `t.val`), and `φ.symm` is continuous on `φ.target`.
        have h_seg_cont : Continuous fun t : unitInterval =>
            affineSegment (φ p) (φ q) t.val :=
          ((contDiff_affineSegment (φ p) (φ q)).continuous).comp
            continuous_subtype_val
        -- `φ.symm` restricted to `φ.target` is continuous (as the
        -- partial inverse of a homeomorphism).
        have h_symm_cont : ContinuousOn (φ.symm : ℂ → X) φ.target :=
          φ.continuousOn_invFun
        refine h_symm_cont.comp_continuous h_seg_cont (fun t => h_line _)
      source' := by
        show φ.symm (affineSegment (φ p) (φ q) (0 : unitInterval).val) = p
        have h0 : (0 : unitInterval).val = (0 : ℝ) := rfl
        rw [h0, affineSegment_zero]
        exact φ.left_inv hp
      target' := by
        show φ.symm (affineSegment (φ p) (φ q) (1 : unitInterval).val) = q
        have h1 : (1 : unitInterval).val = (1 : ℝ) := rfl
        rw [h1, affineSegment_one]
        exact φ.left_inv hq }
  smooth := by
    refine ⟨fun t : ℝ => φ.symm (affineSegment (φ p) (φ q) t), ?_, ?_⟩
    · -- Smoothness of the ambient `ℝ → X` at C^∞ level.
      -- The chart-inverse provides ω-smoothness; we downcast to C^∞
      -- (= `∞ : WithTop ℕ∞`) via `ContMDiffAt.of_le` since `∞ ≤ ω`.
      have h_max : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ⊤ X :=
        IsManifold.subset_maximalAtlas (n := ⊤) h_atlas
      have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (φ.symm : ℂ → X) φ.target :=
        contMDiffOn_symm_of_mem_maximalAtlas h_max
      intro t
      have h_seg_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ⊤ (affineSegment (φ p) (φ q)) t :=
        (contMDiff_affineSegment (φ p) (φ q)) t
      have h_in : affineSegment (φ p) (φ q) t ∈ φ.target := h_line t
      have h_symm_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
          (φ.symm : ℂ → X) (affineSegment (φ p) (φ q) t) :=
        (h_symm _ h_in).contMDiffAt (φ.open_target.mem_nhds h_in)
      have h_comp_top : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ⊤
          (fun t => φ.symm (affineSegment (φ p) (φ q) t)) t :=
        h_symm_at.comp t h_seg_at
      -- Downcast: ω ≥ ∞ in `WithTop ℕ∞`, so `ContMDiffAt ⊤ ⇒ ContMDiffAt ∞`.
      exact h_comp_top.of_le (by decide)
    · -- Agreement on `unitInterval`: by definition of `toPath`.
      intro t
      rfl

/-! ## Source / target identities -/

@[simp] lemma SmoothPath.linearInChart_src
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_line : ∀ t : ℝ, affineSegment (φ p) (φ q) t ∈ φ.target) :
    (SmoothPath.linearInChart φ h_atlas p q hp hq h_line).src = p := rfl

@[simp] lemma SmoothPath.linearInChart_tgt
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_line : ∀ t : ℝ, affineSegment (φ p) (φ q) t ∈ φ.target) :
    (SmoothPath.linearInChart φ h_atlas p q hp hq h_line).tgt = q := rfl

/-! ## Bumped (smoothTransition-reparameterised) affine segment

The C^∞ refactor of `SmoothPath` lets us reparameterise the affine
segment by `Real.smoothTransition` so the image of `bumpedSegment a b`
on all of `ℝ` lies in the closed segment from `a` to `b`. This is
what makes the segment-in-target `linearInChartSegment` constructor
possible — segment-in-target is the natural hypothesis for cover
arguments with convex chart targets. -/

/-- The smooth-bumped affine segment `(1 - σ t) • a + σ t • b`, where
`σ = Real.smoothTransition`. C^∞ globally on `ℝ`; equals `a` at `t = 0`
and `b` at `t = 1`; image of `ℝ` is contained in the closed segment
from `a` to `b`. -/
def bumpedSegment (a b : ℂ) (t : ℝ) : ℂ :=
  (1 - Real.smoothTransition t) • a + Real.smoothTransition t • b

@[simp] lemma bumpedSegment_zero (a b : ℂ) : bumpedSegment a b 0 = a := by
  simp [bumpedSegment, Real.smoothTransition.zero]

@[simp] lemma bumpedSegment_one (a b : ℂ) : bumpedSegment a b 1 = b := by
  simp [bumpedSegment, Real.smoothTransition.one]

/-- `bumpedSegment a b t` lies in `segment ℝ a b` (the closed convex
hull `{(1-s) • a + s • b : s ∈ [0,1]}`) for every `t : ℝ`. Witnessed
by `s = Real.smoothTransition t`, which is in `[0, 1]`. -/
lemma bumpedSegment_mem_segment (a b : ℂ) (t : ℝ) :
    bumpedSegment a b t ∈ segment ℝ a b := by
  refine ⟨1 - Real.smoothTransition t, Real.smoothTransition t,
    ?_, Real.smoothTransition.nonneg _, ?_, rfl⟩
  · linarith [Real.smoothTransition.le_one t]
  · ring

/-- **`bumpedSegment a b` is C^∞ as a function `ℝ → ℂ`.** Stated at
the regularity `∞ : WithTop ℕ∞` matching the `SmoothPath` refactor.
`Real.smoothTransition` is C^∞ at every `n : ℕ∞`; multiplication and
addition by constants preserve C^∞. -/
lemma contDiff_bumpedSegment (a b : ℂ) :
    ContDiff ℝ ∞ (bumpedSegment a b) := by
  unfold bumpedSegment
  have h_sigma : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have h₁ : ContDiff ℝ ∞ (fun t : ℝ => (1 - Real.smoothTransition t) • a) :=
    ((contDiff_const (c := (1 : ℝ))).sub h_sigma).smul contDiff_const
  have h₂ : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition t • b) :=
    h_sigma.smul contDiff_const
  exact h₁.add h₂

/-- Manifold-side C^∞-smoothness of `bumpedSegment`. -/
lemma contMDiff_bumpedSegment (a b : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞ (bumpedSegment a b) :=
  (contDiff_bumpedSegment a b).contMDiff

/-! ## `SmoothPath.linearInChartSegment` -/

/-- **Segment-in-chart smooth path (C^∞ regularity).** Given a chart
`φ` of `X` in `atlas ℂ X`, two points `p q : X` in `φ.source`, and the
hypothesis that the *closed segment* from `φ p` to `φ q` lies in
`φ.target`, build a `SmoothPath 𝓘(ℝ, ℂ) X` from `p` to `q`. The
ambient is `f t = φ.symm (bumpedSegment (φ p) (φ q) t)`, well-defined
on all of `ℝ` because `bumpedSegment _ _ t ∈ segment ℝ (φ p) (φ q)`
for every `t : ℝ`. This is the strict weakening of `linearInChart`'s
"line in target" hypothesis enabled by the C^∞ regularity refactor. -/
noncomputable def SmoothPath.linearInChartSegment
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
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
    · -- C^∞ smoothness of the ambient `ℝ → X`.
      have h_max : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ⊤ X :=
        IsManifold.subset_maximalAtlas (n := ⊤) h_atlas
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
      -- Downcast chart inverse from ω to C^∞.
      have h_symm_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
          (φ.symm : ℂ → X) (bumpedSegment (φ p) (φ q) t) :=
        h_symm_at_top.of_le (by decide)
      exact h_symm_at.comp t h_seg_at
    · -- Agreement on `unitInterval` is by definition of `toPath`.
      intro t
      rfl

/-! ## Source / target identities (segment variant) -/

@[simp] lemma SmoothPath.linearInChartSegment_src
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_seg : segment ℝ (φ p) (φ q) ⊆ φ.target) :
    (SmoothPath.linearInChartSegment φ h_atlas p q hp hq h_seg).src = p := rfl

@[simp] lemma SmoothPath.linearInChartSegment_tgt
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (p q : X) (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (h_seg : segment ℝ (φ p) (φ q) ⊆ φ.target) :
    (SmoothPath.linearInChartSegment φ h_atlas p q hp hq h_seg).tgt = q := rfl

end JacobianChallenge

end
