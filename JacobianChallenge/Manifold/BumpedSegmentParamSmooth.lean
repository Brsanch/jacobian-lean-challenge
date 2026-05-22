/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothness

set_option linter.unusedSectionVars false

/-! # Joint `C^∞`-smoothness of `bumpedSegment` and `chartCoordVelocity` in `(z, t)`

`ChartLocalPrimitiveSmoothness.lean` ships the joint **continuity** of
the parametric maps `(z, t) ↦ bumpedSegment z₀ z t` and
`(z, t) ↦ chartCoordVelocity z₀ z t` on `ℂ × ℝ`. The FTC arc for
`pathPrimitive` needs the strict upgrade to joint **`C^∞`-smoothness**
of the same maps. The integrand of the chart-local primitive's
explicit interval-integral representation factors through these two
parametric pieces; once both are `C^∞`, mathlib's parameter-integral
smoothness theorem upgrades chart-local-primitive continuity to
chart-local-primitive smoothness, which is the missing input of
`ChartLocalPrimitiveSmoothExt`.

## What this file ships

* `contDiff_bumpedSegment_param` — `(p : ℂ × ℝ) ↦ bumpedSegment z₀ p.1 p.2`
  is `C^∞` on `ℂ × ℝ`.
* `contDiff_chartCoordVelocity_param` — `(p : ℂ × ℝ) ↦ chartCoordVelocity z₀ p.1 p.2`
  is `C^∞` on `ℂ × ℝ`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

/-- **Joint `C^∞`-smoothness of `bumpedSegment` parameterised in `(z, t)`.**

`bumpedSegment z₀ z t = (1 - σ t) • z₀ + σ t • z` for
`σ = Real.smoothTransition`. As a function `(z, t) : ℂ × ℝ → ℂ`, it
is `C^∞`: `σ ∘ snd` is `C^∞`, `(1 - σ ∘ snd) • z₀` is `C^∞` as a
scalar-multiple-by-constant, and `(σ ∘ snd) • fst` is `C^∞` as a
bilinear product of two `C^∞` maps. -/
lemma contDiff_bumpedSegment_param (z₀ : ℂ) :
    ContDiff ℝ ∞ (fun p : ℂ × ℝ => bumpedSegment z₀ p.1 p.2) := by
  -- `σ ∘ snd` is `C^∞` on `ℂ × ℝ`.
  have h_sigma_snd : ContDiff ℝ ∞ (fun p : ℂ × ℝ => Real.smoothTransition p.2) :=
    Real.smoothTransition.contDiff.comp contDiff_snd
  -- `1 - σ ∘ snd` is `C^∞`.
  have h_one_minus : ContDiff ℝ ∞ (fun p : ℂ × ℝ => 1 - Real.smoothTransition p.2) :=
    contDiff_const.sub h_sigma_snd
  -- First summand: `(1 - σ ∘ snd) • z₀` (scalar varies, vector constant).
  have h_first : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => (1 - Real.smoothTransition p.2) • z₀) :=
    h_one_minus.smul contDiff_const
  -- Second summand: `(σ ∘ snd) • fst` (scalar and vector both vary).
  have h_second : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => Real.smoothTransition p.2 • p.1) :=
    h_sigma_snd.smul contDiff_fst
  -- Sum is `C^∞`.
  exact h_first.add h_second

/-- **Joint `C^∞`-smoothness of `chartCoordVelocity` parameterised in `(z, t)`.**

`chartCoordVelocity z₀ z t = ((σ' t : ℝ) : ℂ) * (z - z₀)`. As a
function `(z, t) : ℂ × ℝ → ℂ`, it is `C^∞`:
* `σ' = deriv Real.smoothTransition` is `C^∞` on `ℝ` (since `σ` is
  `C^∞` and the derivative of a `C^∞` function is `C^∞`).
* `σ' ∘ snd` is `C^∞` on `ℂ × ℝ`.
* `(σ' ∘ snd : ℝ → ℂ)` cast through `Complex.ofReal` is `C^∞`.
* `fst - z₀` is `C^∞` (linear in `fst`).
* The product is `C^∞`. -/
lemma contDiff_chartCoordVelocity_param (z₀ : ℂ) :
    ContDiff ℝ ∞ (fun p : ℂ × ℝ => chartCoordVelocity z₀ p.1 p.2) := by
  unfold chartCoordVelocity
  -- `σ` is `C^∞`; `deriv σ` is `C^∞`.
  have h_sigma : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have h_deriv_sigma : ContDiff ℝ ∞ (deriv Real.smoothTransition) := by
    -- For `C^∞` functions on ℝ, the derivative is `C^∞`.
    -- In the `WithTop ℕ∞` regularity world, `∞ + 1 = ∞`.
    have := h_sigma.iterate_deriv 1
    simpa using this
  -- `deriv σ ∘ snd` is `C^∞` on `ℂ × ℝ`.
  have h_deriv_sigma_snd : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => deriv Real.smoothTransition p.2) :=
    h_deriv_sigma.comp contDiff_snd
  -- Cast to ℂ via `Complex.ofRealCLM`.
  have h_ofReal_cd : ContDiff ℝ ∞ (Complex.ofRealCLM : ℝ → ℂ) :=
    Complex.ofRealCLM.contDiff
  have h_cast : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => ((deriv Real.smoothTransition p.2 : ℝ) : ℂ)) := by
    have := h_ofReal_cd.comp h_deriv_sigma_snd
    simpa [Complex.ofRealCLM_apply] using this
  -- `fst - z₀` is `C^∞`.
  have h_sub : ContDiff ℝ ∞ (fun p : ℂ × ℝ => p.1 - z₀) :=
    contDiff_fst.sub contDiff_const
  -- Product of two `C^∞` ℂ-valued maps is `C^∞`.
  exact h_cast.mul h_sub

end JacobianChallenge

end
