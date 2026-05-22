/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalIntegrandSmooth

set_option linter.unusedSectionVars false

/-! # Real and imaginary parts of the chart-coord integrand are jointly `C^∞`

`ChartLocalIntegrandSmooth.lean` ships joint `ContDiffOn ℝ ∞` of the
full chart-coord integrand product
`(z, t) ↦ f(bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t` on
`S × Set.univ`.

The chart-local primitive's real-valued interval-integral
representation needs the real and imaginary parts of this complex-
valued integrand to be `ContDiffOn ℝ ∞` separately, since mathlib's
`intervalIntegral` parameter-derivative theorems operate on real- and
complex-Banach-valued integrands. Both parts are `ContDiffOn ℝ ∞` by
composing with `Complex.reCLM` / `Complex.imCLM` (continuous
ℝ-linear maps, hence `ContDiff ℝ ⊤`).

## What this file ships

* `contDiffOn_chartLocalIntegrand_re_param` — joint `ContDiffOn ℝ ∞`
  of the real-part integrand
  `(z, t) ↦ (f(bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t).re`.
* `contDiffOn_chartLocalIntegrand_im_param` — joint `ContDiffOn ℝ ∞`
  of the imaginary-part integrand.

These are the ℝ-valued integrand-side smoothness inputs the parameter-
integral upgrade will consume.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

/-- **Real part of the chart-coord integrand product is jointly
`ContDiffOn ℝ ∞`.**

Composes `contDiffOn_chartLocalIntegrand_param` with
`Complex.reCLM.contDiff` (continuous ℝ-linear map from `ℂ` to `ℝ`,
`C^∞`) via `ContDiff.comp_contDiffOn`. -/
lemma contDiffOn_chartLocalIntegrand_re_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hf : ContDiffOn ℝ ∞ f S) (hS : Convex ℝ S)
    (z₀ : ℂ) (hz₀ : z₀ ∈ S) :
    ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ =>
        (f (bumpedSegment z₀ p.1 p.2) * chartCoordVelocity z₀ p.1 p.2).re)
      (S ×ˢ Set.univ) := by
  have h_full := contDiffOn_chartLocalIntegrand_param hf hS z₀ hz₀
  have h_re : ContDiff ℝ ∞ Complex.reCLM := Complex.reCLM.contDiff
  exact h_re.comp_contDiffOn h_full

/-- **Imaginary part of the chart-coord integrand product is jointly
`ContDiffOn ℝ ∞`.**

Composes `contDiffOn_chartLocalIntegrand_param` with
`Complex.imCLM.contDiff` analogously. -/
lemma contDiffOn_chartLocalIntegrand_im_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hf : ContDiffOn ℝ ∞ f S) (hS : Convex ℝ S)
    (z₀ : ℂ) (hz₀ : z₀ ∈ S) :
    ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ =>
        (f (bumpedSegment z₀ p.1 p.2) * chartCoordVelocity z₀ p.1 p.2).im)
      (S ×ˢ Set.univ) := by
  have h_full := contDiffOn_chartLocalIntegrand_param hf hS z₀ hz₀
  have h_im : ContDiff ℝ ∞ Complex.imCLM := Complex.imCLM.contDiff
  exact h_im.comp_contDiffOn h_full

end JacobianChallenge

end
