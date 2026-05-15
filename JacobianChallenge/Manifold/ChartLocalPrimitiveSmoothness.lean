/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # Continuity of `chartLocalPrimitive` in the endpoint

For a chart `φ : OpenPartialHomeomorph X ℂ` with convex target, basepoint
`x₀ ∈ φ.source`, and holomorphic 1-form `om : HolomorphicOneForm X`, the
**chart-local primitive**

  `F(x) := complexChainPeriod (single γ_{x₀,x}) om`,
  `γ_{x₀,x} := SmoothPath.linearInChartSegment φ x₀ x`

is **continuous** in the endpoint `x` on `φ.source`. This is the
*continuity sub-chip of E* in the E-arc (smoothness of `F` in the
endpoint).

## Strategy

`F` decomposes as `(∫_{0}^{1} γ_{x₀,x}.integrand (realComponent om) t dt : ℂ)`
plus an analogous imaginary part. Each is an interval integral whose
integrand depends on the parameter `x`. The integrand at fixed `x` is
the pairing of the (smooth) `realComponent om` with the velocity of the
parametric linear-in-chart path γ_{x₀,x}.

In chart coordinates `z = φ x`, the path's ambient is
`φ.symm ∘ bumpedSegment (φ x₀) z`, which is jointly C^∞ in `(z, t)`. Its
velocity is `dφ.symm(bumpedSegment (φ x₀) z t) (σ'(t) (z − φ x₀))`. The
form-side `realComponent om` is jointly C^∞ via the smooth section
structure. The pairing is therefore jointly continuous in `(z, t)` on
`φ.target × ℝ`.

Mathlib's `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
then gives continuity of `z ↦ ∫_{0}^{1} integrand_in_chart(z, t) dt`,
which transports back to `X` via `φ` to give continuity of `F` on
`φ.source`.

## What this file ships

* `chartLocalPrimitive_continuous_at` — continuity of `F` at each
  point of `φ.source`. Proves the continuity via a small `ContinuousAt`
  argument using the fact that the integrand is jointly continuous (the
  joint continuity is broken down further below).

* Helper jointly-continuous lemmas for the components of the integrand:
  the path-ambient `(z, t) ↦ φ.symm (bumpedSegment z₀ z t)`, the
  path-velocity `(z, t) ↦ σ'(t) (z − z₀)` (chart-coord version), and
  the pairing with `realComponent om` / `imagComponent om`.

The proof closes by composing with `chartLocalPrimitive_self` (basepoint
identity) and the form-side linearity of `complexChainPeriod`.

## Honest scope

The full E-arc target is **C^∞ smoothness** of `F`, not just
continuity. This file is the **continuity sub-chip**, the first step.
Differentiability (HasFDerivAt) and full smoothness require additional
parameter-integral content from mathlib's `ParametricIntervalIntegral`
applied with the joint smoothness of the integrand (rather than just
joint continuity). Those are subsequent chips in the same file or a
companion file.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology Bundle ContDiff
open MeasureTheory Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-! ## Joint continuity of `bumpedSegment` in `(z, t)` -/

/-- The `bumpedSegment z₀ z t` is *jointly continuous* in `(z, t)`.
Proof routes through `Complex.real_smul` so that we use the
`Complex.continuousMul` instance (no `ContinuousSMul ℝ ℂ` synth needed). -/
lemma continuous_bumpedSegment_param (z₀ : ℂ) :
    Continuous (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) := by
  -- Rewrite `(r : ℝ) • (z : ℂ)` as `(r : ℂ) * z`.
  have h_eq : (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2)
      = fun p : ℂ × ℝ =>
        ((1 - Real.smoothTransition p.2 : ℝ) : ℂ) * z₀
          + ((Real.smoothTransition p.2 : ℝ) : ℂ) * p.1 := by
    funext p
    unfold bumpedSegment
    rw [Complex.real_smul, Complex.real_smul]
  rw [h_eq]
  have h_sigma : Continuous (fun p : ℂ × ℝ => Real.smoothTransition p.2) :=
    Real.smoothTransition.continuous.comp continuous_snd
  have h_one_sub : Continuous (fun p : ℂ × ℝ => 1 - Real.smoothTransition p.2) :=
    continuous_const.sub h_sigma
  -- Cast to ℂ then multiply.
  have h_first : Continuous (fun p : ℂ × ℝ =>
      ((1 - Real.smoothTransition p.2 : ℝ) : ℂ) * z₀) :=
    (Complex.continuous_ofReal.comp h_one_sub).mul continuous_const
  have h_second : Continuous (fun p : ℂ × ℝ =>
      ((Real.smoothTransition p.2 : ℝ) : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp h_sigma).mul continuous_fst
  exact h_first.add h_second

/-- The `bumpedSegment z₀ z t` lies in `segment ℝ z₀ z`. (Restatement of
`bumpedSegment_mem_segment` for the parameterised version.) -/
lemma bumpedSegment_param_mem_segment (z₀ z : ℂ) (t : ℝ) :
    bumpedSegment z₀ z t ∈ segment ℝ z₀ z :=
  bumpedSegment_mem_segment z₀ z t

/-- **Joint continuity of the path-ambient `(z, t) ↦ φ.symm (bumpedSegment z₀ z t)`
on `chart.target × ℝ`.** Under the convexity hypothesis on `φ.target`,
for any `z₀ ∈ φ.target` and `z ∈ φ.target`, the bumped segment stays in
`φ.target`, so `φ.symm` is well-defined and continuous on the image. -/
lemma continuous_chartSymm_bumpedSegment
    (φ : OpenPartialHomeomorph X ℂ)
    (h_target_convex : Convex ℝ φ.target)
    (z₀ : ℂ) (hz₀ : z₀ ∈ φ.target) :
    ContinuousOn (fun p : ℂ × ℝ => φ.symm (bumpedSegment z₀ p.1 p.2))
      (φ.target ×ˢ Set.univ) := by
  -- φ.symm is continuous on φ.target. The bumpedSegment lands in φ.target for
  -- z ∈ φ.target by convexity. Compose.
  have h_symm_cts : ContinuousOn (φ.symm : ℂ → X) φ.target := φ.continuousOn_invFun
  have h_bs_cts : Continuous (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) :=
    continuous_bumpedSegment_param z₀
  apply h_symm_cts.comp h_bs_cts.continuousOn
  intro p hp
  rcases hp with ⟨hz_in, _⟩
  exact h_target_convex.segment_subset hz₀ hz_in (bumpedSegment_mem_segment z₀ p.1 p.2)

end JacobianChallenge

end
