/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option linter.unusedSectionVars false

/-! # Holomorphic change of variables for planar integrals (Arc 1, chip 2b)

For an injective holomorphic `f` on a measurable `s ⊆ ℂ`,

  `∫_{f(s)} g(w) dA(w) = ∫_s |f′(z)|² · g(f(z)) dA(z)`.

This is the chart-overlap substitution rule of the L²-Hodge-lite route
(`HANDOFF_ITEM14.md`, ACTIVE ARC): the real Jacobian determinant of a
holomorphic map is `|f′|² = normSq f′`, which is exactly the
`(0,1)-coefficient × conjugate-coefficient × area` transformation
weight. It is what collapses the per-chart sum defining the L² pairing
into a chart-independent quantity on overlaps.

## Proof

mathlib's general change of variables
(`integral_image_eq_integral_abs_det_fderiv_smul`) with the ℝ-linear
derivative `f′ z • (1 : ℂ →L[ℝ] ℂ)` supplied by
`HasDerivAt.complexToReal_fderiv`. Its determinant is computed in the
basis `{1, I}`: the matrix of multiplication-by-`c` is
`[[re c, −im c], [im c, re c]]` with determinant `normSq c`. (The
basis route deliberately avoids `restrictScalars`/`Algebra.norm`,
which hit the `IsScalarTower ℝ ℂ ℂ` instance diamond — see
`feedback_jacobian_complex_real_diamond`.)

## What this file ships

* `HolomorphicCoV.det_smul_one_CLM` — the real Jacobian determinant of
  multiplication by `c` is `normSq c`.
* `HolomorphicCoV.setIntegral_image_eq_integral_normSq_deriv_mul` —
  the substitution rule (explicit-derivative form).
* `HolomorphicCoV.setIntegral_image_eq_of_differentiableOn` — the
  open-set / `deriv` form for chart transitions.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory
open scoped Topology

namespace JacobianChallenge

namespace HolomorphicCoV

/-- **The real Jacobian determinant of complex multiplication.** The
ℝ-linear endomorphism `c • (1 : ℂ →L[ℝ] ℂ)` of ℂ (multiplication by
`c`) has determinant `normSq c = |c|²`. Computed in the basis
`{1, I}`. -/
lemma det_smul_one_CLM (c : ℂ) :
    (c • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq c := by
  have hmat : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)).det = Complex.normSq c := by
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.coe_basisOneI_repr, Complex.normSq_apply]
    show (c * 1).re * (c * Complex.I).im
        - (c * Complex.I).re * (c * 1).im = c.re * c.re + c.im * c.im
    simp only [mul_one, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  calc (c • (1 : ℂ →L[ℝ] ℂ)).det
      = LinearMap.det ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) := rfl
    _ = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)).det :=
        (LinearMap.det_toMatrix Complex.basisOneI _).symm
    _ = Complex.normSq c := hmat

/-- **Holomorphic substitution rule** (explicit-derivative form): for
injective `f` with `HasDerivAt f (f′ z) z` at every `z` of a
measurable `s`,

  `∫_{f''s} g = ∫_s normSq (f′ z) · g (f z)`.

The weight is stated in coerce-mul form `(↑(normSq …)) * ·` (not `•`)
per the repo's smul-diamond convention. -/
theorem setIntegral_image_eq_integral_normSq_deriv_mul
    {f f' : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z) (hinj : Set.InjOn f s)
    (g : ℂ → ℂ) :
    ∫ w in f '' s, g w ∂volume
      = ∫ z in s, ((Complex.normSq (f' z) : ℝ) : ℂ) * g (f z) ∂volume := by
  have hF : ∀ z ∈ s, HasFDerivWithinAt f
      (f' z • (1 : ℂ →L[ℝ] ℂ)) s z := fun z hz =>
    ((hf z hz).complexToReal_fderiv).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hF hinj g]
  apply setIntegral_congr_fun hs
  intro z _
  show |(f' z • (1 : ℂ →L[ℝ] ℂ)).det| • g (f z)
    = ((Complex.normSq (f' z) : ℝ) : ℂ) * g (f z)
  rw [det_smul_one_CLM, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact Complex.real_smul

/-- **Holomorphic substitution rule, chart-transition form**: for `f`
holomorphic and injective on an open `U`,

  `∫_{f''U} g = ∫_U normSq (deriv f z) · g (f z)`. -/
theorem setIntegral_image_eq_of_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) (g : ℂ → ℂ) :
    ∫ w in f '' U, g w ∂volume
      = ∫ z in U, ((Complex.normSq (deriv f z) : ℝ) : ℂ) * g (f z)
          ∂volume :=
  setIntegral_image_eq_integral_normSq_deriv_mul hU.measurableSet
    (fun z hz => ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt)
    hinj g

end HolomorphicCoV

end JacobianChallenge

end
