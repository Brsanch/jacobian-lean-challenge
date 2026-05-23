/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The antiholomorphic (Wirtinger) derivative `∂̄` on `ℂ → ℂ`

The Forster §16 route to `ExistsSimplePoleGermAtSomePoint X` at genus 0
needs the antiholomorphic derivative
`∂̄ f z := ½ ((fderiv ℝ f z) 1 + I · (fderiv ℝ f z) I)`
in three concrete ways:

* to compute `∂̄(χ · g₀)` where `χ` is a smooth cutoff and `g₀ = 1/φ`
  is the chart-local pole — by Leibniz and holomorphy of `g₀` off the
  pole, `∂̄(χ · g₀) = (∂̄ χ) · g₀` on the locus where `g₀` is
  holomorphic (the support of `dχ`);
* to characterise holomorphy as `∂̄ f = 0` via Cauchy-Riemann;
* to state `DBarSolvabilityAtGenusZero` in a later session.

This file works **chart-locally**, i.e. on functions `ℂ → ℂ`. The
manifold-wide `(0,1)`-form formulation is a separate piece of theory
(the chain-rule for `∂̄` under a holomorphic transition picks up a
conjugate-derivative factor, making `∂̄ u` a section of the
`(0,1)`-form bundle, not a function); it lives in a later file. Here
we only need the algebraic operator and its Leibniz / CR identities.

## Main definitions

* `JacobianChallenge.partialZBar f z := ½ ((fderiv ℝ f z) 1 + I · (fderiv ℝ f z) I)`

## Main results

* `partialZBar_const`, `partialZBar_add`, `partialZBar_neg`, `partialZBar_sub`
* `partialZBar_mul` (Leibniz)
* `partialZBar_eq_zero_of_differentiableAt` — `∂̄ f z = 0` when `f` is
  complex-differentiable at `z` (Cauchy-Riemann)
* `partialZBar_mul_of_differentiableAt_right` — the Forster §16
  specialization: `∂̄(f · g) z = (∂̄ f z) · g z` when `g` is holomorphic
  at `z`.
-/

namespace JacobianChallenge

open Complex

/-- Manually-constructed `IsScalarTower ℝ ℂ ℂ`. Mathlib's instance synth
doesn't find this in `restrictScalars`-call contexts (an `IsScalarTower
ℝ ℂ ℂ` diamond — see `Manifold/MFDerivComplexToRealApply.lean` for the
canonical workaround). We pass it explicitly to `@`-applied lemmas. -/
@[reducible] private def isScalarTower_R_C_C : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

/-- Wrapper for `DifferentiableAt.restrictScalars ℝ` with explicit
`IsScalarTower ℝ ℂ ℂ` instance. -/
private theorem differentiableAt_restrictScalars_R_C_C
    {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x :=
  @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C
    ℂ _ _ _ isScalarTower_R_C_C _ _ h

/-- The antiholomorphic (Wirtinger) derivative of a real-differentiable
function `f : ℂ → ℂ` at `z`. Defined as
`½ ((fderiv ℝ f z) 1 + I · (fderiv ℝ f z) I)`.

A function `f` is complex-differentiable at `z` iff
`partialZBar f z = 0`; see
`partialZBar_eq_zero_of_differentiableAt`. -/
noncomputable def partialZBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I)

@[simp] lemma partialZBar_const (c : ℂ) (z : ℂ) :
    partialZBar (fun _ : ℂ => c) z = 0 := by
  simp [partialZBar]

lemma partialZBar_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZBar (f + g) z = partialZBar f z + partialZBar g z := by
  simp only [partialZBar, fderiv_add hf hg, ContinuousLinearMap.add_apply]
  ring

lemma partialZBar_neg {f : ℂ → ℂ} {z : ℂ} :
    partialZBar (-f) z = -(partialZBar f z) := by
  simp only [partialZBar, fderiv_neg, ContinuousLinearMap.neg_apply]
  ring

lemma partialZBar_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZBar (f - g) z = partialZBar f z - partialZBar g z := by
  rw [sub_eq_add_neg, partialZBar_add hf hg.neg, partialZBar_neg, sub_eq_add_neg]

/-- **Leibniz rule** for the antiholomorphic derivative. -/
lemma partialZBar_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    partialZBar (f * g) z = (partialZBar f z) * g z + f z * (partialZBar g z) := by
  have hmul : fderiv ℝ (f * g) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  have h1 : (fderiv ℝ (f * g) z) 1
      = f z * (fderiv ℝ g z) 1 + g z * (fderiv ℝ f z) 1 := by
    rw [hmul]; simp [smul_eq_mul]
  have hI : (fderiv ℝ (f * g) z) I
      = f z * (fderiv ℝ g z) I + g z * (fderiv ℝ f z) I := by
    rw [hmul]; simp [smul_eq_mul]
  simp only [partialZBar, h1, hI]
  ring

/-- **Cauchy-Riemann:** if `f` is complex-differentiable at `z`, then
`∂̄ f z = 0`. -/
lemma partialZBar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : partialZBar f z = 0 := by
  obtain ⟨_, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp hf
  -- hCR : fderiv ℝ f z I = I • fderiv ℝ f z 1
  simp only [partialZBar, hCR, smul_eq_mul]
  have hII : I * (I * fderiv ℝ f z 1) = -(fderiv ℝ f z 1) := by
    rw [← mul_assoc, I_mul_I]; ring
  rw [hII]; ring

/-- **Forster §16 specialization:** if `g` is complex-differentiable
at `z` (i.e., holomorphic at `z`), then `∂̄(f · g) z = (∂̄ f z) · g z`.
This is the identity that lets `∂̄(χ · g₀) = (∂̄ χ) · g₀` on the locus
where the chart-local pole `g₀` is holomorphic — i.e., off the simple
pole. The support of the right-hand side is the support of `dχ`, which
the smooth cutoff arranges to be compact and away from the pole. -/
lemma partialZBar_mul_of_differentiableAt_right {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℂ g z) :
    partialZBar (f * g) z = (partialZBar f z) * g z := by
  have hgR : DifferentiableAt ℝ g z := differentiableAt_restrictScalars_R_C_C hg
  rw [partialZBar_mul hf hgR, partialZBar_eq_zero_of_differentiableAt hg]
  ring

/-- Symmetric specialization: if `f` is complex-differentiable at `z`,
then `∂̄(f · g) z = f z · (∂̄ g z)`. -/
lemma partialZBar_mul_of_differentiableAt_left {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℝ g z) :
    partialZBar (f * g) z = f z * (partialZBar g z) := by
  have hfR : DifferentiableAt ℝ f z := differentiableAt_restrictScalars_R_C_C hf
  rw [partialZBar_mul hfR hg, partialZBar_eq_zero_of_differentiableAt hf]
  ring

end JacobianChallenge
