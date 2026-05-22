/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasFDerivAtRestrictScalarsComplex

set_option linter.unusedSectionVars false

/-! # `fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ` for `f : ℂ → ℂ`

`HasFDerivAtRestrictScalarsComplex.lean` ships the hand-rolled
`HasFDerivAt.restrictScalarsComplex` bridge. This file derives the
`fderiv` identity that the bridge implies under
`DifferentiableAt ℂ f x` (resp. `DifferentiableWithinAt ℂ f s x`),
using mathlib's uniqueness of Fréchet derivatives.

The identity is the building block for the eventual iterated-derivative
recursion that lifts the bridge to `ContDiffOn ℝ n f s` for arbitrary
`n : ℕ`. Each step in the recursion will rewrite `fderiv ℝ f` as
`(fderiv ℂ f).restrictScalars ℝ` and apply the bridge to the
ℂ-differentiable side.

## What this file ships

* `fderiv_real_eq_fderiv_complex_restrictScalars` — pointwise identity
  `fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ` for `f : ℂ → ℂ`
  under `DifferentiableAt ℂ f x`.
* `fderivWithin_real_eq_fderivWithin_complex_restrictScalars` —
  `fderivWithin` version under `DifferentiableWithinAt ℂ f s x` plus
  `UniqueDiffWithinAt ℝ s x`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology

/-- **fderiv identity for `f : ℂ → ℂ` under `DifferentiableAt ℂ`.**

The ℝ-Fréchet derivative of `f` at `x` is the scalar-restriction of the
ℂ-Fréchet derivative. Proof: `f.hasFDerivAt` (ℂ-side) gives
`HasFDerivAt f (fderiv ℂ f x) x`; the bridge upgrades this to
`HasFDerivAt f ((fderiv ℂ f x).restrictScalars ℝ) x`; uniqueness of
`fderiv` (mathlib `HasFDerivAt.fderiv`) closes. -/
theorem fderiv_real_eq_fderiv_complex_restrictScalars
    {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ := by
  have h_C : HasFDerivAt f (fderiv ℂ f x) x := h.hasFDerivAt
  have h_R : HasFDerivAt f ((fderiv ℂ f x).restrictScalars ℝ) x :=
    h_C.restrictScalarsComplex
  exact h_R.fderiv

/-- **fderivWithin identity for `f : ℂ → ℂ` under
`DifferentiableWithinAt ℂ` + `UniqueDiffWithinAt ℝ`.**

The ℝ-Fréchet-within derivative of `f` at `x ∈ s` is the
scalar-restriction of the ℂ-Fréchet-within derivative, provided `s` has
unique-diff structure at `x` in the ℝ sense. -/
theorem fderivWithin_real_eq_fderivWithin_complex_restrictScalars
    {f : ℂ → ℂ} {s : Set ℂ} {x : ℂ}
    (h : DifferentiableWithinAt ℂ f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x = (fderivWithin ℂ f s x).restrictScalars ℝ := by
  have h_C : HasFDerivWithinAt f (fderivWithin ℂ f s x) s x :=
    h.hasFDerivWithinAt
  have h_R : HasFDerivWithinAt f ((fderivWithin ℂ f s x).restrictScalars ℝ) s x :=
    h_C.restrictScalarsComplex
  exact h_R.fderivWithin hs

end
