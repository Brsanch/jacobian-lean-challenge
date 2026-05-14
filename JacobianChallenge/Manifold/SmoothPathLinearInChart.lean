/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.SmoothChain

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth-path-connectedness primitive 2: `SmoothPath.linearInChart`

Builds a `SmoothPath` between two points `p q : X` whose
chart-coordinate connecting line lies entirely inside the chart
target. The construction is genuinely analytic: it produces a
`SmoothPath 𝓘(ℝ, ℂ) X` at the ω-regularity level required by the
`SmoothPath` structure (ContMDiff at `⊤ : WithTop ℕ∞`, which is the
analytic level `ω` per `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`).

## Why the strong "line in target" hypothesis

The `SmoothPath` structure demands a globally smooth ambient
`f : ℝ → X` at ω-regularity. Analytic functions are determined by
their germs, so a globally analytic `f` cannot be constant on a
half-line — meaning the standard C^∞ trick of smoothly extending by
constants outside `[0, 1]` does *not* produce an analytic path. For
the affine chart-coordinate construction to extend to all of `ℝ`, the
chart target must already contain the entire line through `φ p` and
`φ q`, not merely the segment.

This restriction is genuine: there is no chart-cover argument that
weakens the hypothesis to "segment in target" at the ω level without
either changing the `SmoothPath` definition (e.g., downgrading to
C^∞) or invoking a non-trivial analytic-continuation argument.

The hypothesis *does* hold when the chart target is the entire model
space `ℂ` — notably the affine chart of `RiemannSphere`, whose target
is `ℂ` and whose source is `RiemannSphere \ {∞}`. For such charts,
`SmoothPath.linearInChart` is unconditional on the choice of
endpoints in `φ.source`.

## What this file delivers

* `affineSegment a b t : ℂ` — the affine combination `(1 - t) • a + t • b`.
* `contDiff_affineSegment` — affineSegment is `C^ω` jointly in `t`.
* `affineSegment_zero` / `affineSegment_one` — endpoint identities.
* `SmoothPath.linearInChart` — constructor of a `SmoothPath 𝓘(ℝ, ℂ) X`
  from a chart `φ` whose target contains the entire line through
  `φ p, φ q`, plus the membership and source/target witnesses.
* `SmoothPath.linearInChart_src` / `_tgt` — source/target identities.

The smoothness proof factors through:

* `contDiff_affineSegment` (analyticity of the affine map),
* `ContDiff.contMDiff` (lifting `ContDiff ℝ ω` to
  `ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ω`),
* `contMDiffAt_symm_of_mem_maximalAtlas` (analyticity of the chart
  inverse on its target),
* `ContMDiffAt.comp` (composition).

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
    · -- Smoothness of the ambient `ℝ → X` at level ω.
      -- Use chart-inverse smoothness composed with the analytic affine
      -- segment. The model on both sides for `φ.symm` is `𝓘(ℝ, ℂ)`
      -- (real-smooth structure on `ℂ`).
      have h_max : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ⊤ X :=
        IsManifold.subset_maximalAtlas (n := ⊤) h_atlas
      have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (φ.symm : ℂ → X) φ.target :=
        contMDiffOn_symm_of_mem_maximalAtlas h_max
      intro t
      -- Reduce to a pointwise ContMDiffAt statement.
      have h_seg_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ⊤ (affineSegment (φ p) (φ q)) t :=
        (contMDiff_affineSegment (φ p) (φ q)) t
      have h_in : affineSegment (φ p) (φ q) t ∈ φ.target := h_line t
      have h_symm_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
          (φ.symm : ℂ → X) (affineSegment (φ p) (φ q) t) :=
        (h_symm _ h_in).contMDiffAt (φ.open_target.mem_nhds h_in)
      exact h_symm_at.comp t h_seg_at
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

end JacobianChallenge

end
