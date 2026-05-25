/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.ReImTopology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-E (Section A): plane ↔ iterated integral

This file ships the **Fubini bridge** that converts between the
two representations of an integral over `ℂ`:

* **Plane form** — `∫ ζ : ℂ, f ζ ∂volume` (Bochner integral against
  Lebesgue measure on `ℂ`, defined via the inner-product structure).
* **Iterated form** — `∫ x in -L..L, ∫ y in -L..L, f((x:ℂ) + y * I)`
  (the form mathlib's rectangle Stokes produces, used in Chip 3c-D).

The bridge holds whenever `f` is integrable and supported in
`Metric.ball 0 L`. It is the input shape for Chip 3c-E's DCT-limit
step, which extracts the Cauchy-Pompeiu identity from Chip 3c-D's
iterated balance equation.

## Main result

* `integral_complex_eq_iteratedIntegral_of_tsupport_in_ball`:
  For `f : ℂ → ℂ` integrable with `tsupport f ⊆ Metric.ball 0 L`,
  ```
  ∫ ζ : ℂ, f ζ ∂volume = ∫ x in -L..L, ∫ y in -L..L, f ((x : ℂ) + y * I).
  ```

## Proof structure

1. Change of variables `ζ ↦ (ζ.re, ζ.im)` via
   `Complex.volume_preserving_equiv_real_prod`.
2. Fubini (`MeasureTheory.integral_prod`).
3. Cut both `ℝ`-integrals to `(-L, L]` using
   `setIntegral_eq_integral_of_forall_compl_eq_zero` (compact support
   in `ball 0 L` implies `f((x:ℂ) + y*I) = 0` whenever `|x| > L` or
   `|y| > L`).
4. Convert set integral to interval integral via
   `intervalIntegral.integral_of_le` + `integral_Ioc_eq_integral_Ioo`
   chain (volume gives `Ioc = Ioo` for a.e. equality, which suffices
   for the Bochner integral).

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Real Topology Interval

namespace JacobianChallenge.PompeiuKernel

/-! ## Geometric helper: `tsupport f ⊆ ball 0 L` implies pointwise
vanishing outside the square `[-L, L] × [-L, L]`. -/

/-- If `tsupport f ⊆ ball 0 L`, then `f ζ = 0` whenever `‖ζ‖ ≥ L`. -/
private lemma eq_zero_of_norm_ge_of_tsupport_in_ball
    {f : ℂ → ℂ} {L : ℝ}
    (h_supp : tsupport f ⊆ Metric.ball 0 L)
    {ζ : ℂ} (hζ : L ≤ ‖ζ‖) :
    f ζ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h_mem
  have h_lt : ‖ζ‖ < L := by
    have := h_supp h_mem
    rw [Metric.mem_ball, dist_zero_right] at this
    exact this
  linarith

/-! ## Plane → ℝ × ℝ change of variables -/

/-- Algebraic identity `(p.1 : ℂ) + p.2 * I = ⟨p.1, p.2⟩` as a function rewrite. -/
private lemma fun_complex_mk_eq (f : ℂ → ℂ) :
    (fun p : ℝ × ℝ => f ((p.1 : ℂ) + p.2 * I))
      = fun p : ℝ × ℝ => f ({ re := p.1, im := p.2 } : ℂ) := by
  funext p
  congr 1
  exact (Complex.mk_eq_add_mul_I p.1 p.2).symm

/-- Change-of-variables: `∫ ζ : ℂ, f ζ = ∫ (p : ℝ × ℝ), f((p.1 : ℂ) + p.2 * I)`. -/
private lemma integral_complex_eq_integral_prod (f : ℂ → ℂ) :
    ∫ ζ : ℂ, f ζ
      = ∫ p : ℝ × ℝ, f ((p.1 : ℂ) + p.2 * I) := by
  have h_mp : MeasurePreserving
      (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm _
  have h_eq := h_mp.integral_comp' (f := Complex.measurableEquivRealProd.symm) f
  -- `h_eq : ∫ p, f (measurableEquivRealProd.symm p) = ∫ ζ, f ζ`.
  rw [fun_complex_mk_eq f, ← h_eq]
  rfl

/-- Integrability transfers from `ℂ` to `ℝ × ℝ` under the change of variables. -/
private lemma integrable_prod_of_integrable_complex
    {f : ℂ → ℂ} (h_int : Integrable f) :
    Integrable (fun p : ℝ × ℝ => f ((p.1 : ℂ) + p.2 * I)) := by
  have h_mp : MeasurePreserving
      (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm _
  have h_emb : MeasurableEmbedding
      (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) :=
    Complex.measurableEquivRealProd.symm.measurableEmbedding
  have h_int' : Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
    (h_mp.integrable_comp_emb h_emb).mpr h_int
  -- `f ∘ measurableEquivRealProd.symm p = f { re := p.1, im := p.2 }`, which equals
  -- `f((p.1:ℂ) + p.2*I)` by `fun_complex_mk_eq`.
  convert h_int' using 1
  exact fun_complex_mk_eq f

/-- Iterated form via Fubini: `∫ p : ℝ × ℝ, f((p.1:ℂ) + p.2*I) = ∫ x, ∫ y, f((x:ℂ) + y*I)`. -/
private lemma integral_prod_eq_iterated
    {f : ℂ → ℂ} (h_int : Integrable f) :
    ∫ p : ℝ × ℝ, f ((p.1 : ℂ) + p.2 * I)
      = ∫ x : ℝ, ∫ y : ℝ, f ((x : ℂ) + y * I) := by
  have h_prod_int := integrable_prod_of_integrable_complex h_int
  -- `volume` on `ℝ × ℝ` is `volume.prod volume` (by defn / `volume_eq_prod`).
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
      (Measure.volume_eq_prod ℝ ℝ)] at h_prod_int
  rw [show ((fun p : ℝ × ℝ => f ((p.1 : ℂ) + p.2 * I)) : ℝ × ℝ → ℂ)
      = (fun p : ℝ × ℝ => (fun x : ℝ => fun y : ℝ =>
          f ((x : ℂ) + y * I)) p.1 p.2) from rfl]
  rw [show ((volume : Measure (ℝ × ℝ))) = ((volume : Measure ℝ).prod volume) from
      Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.integral_prod _ h_prod_int

/-! ## Iterated integral cut to `[-L, L]` -/

/-- The integrand `f((x:ℂ) + y*I)` vanishes when `‖((x:ℂ) + y*I)‖ ≥ L`. In
particular, for `L ≤ |x|`, the entire inner integral vanishes. -/
private lemma inner_integrand_eq_zero_of_abs_re_ge
    {f : ℂ → ℂ} {L : ℝ}
    (h_supp : tsupport f ⊆ Metric.ball 0 L)
    {x : ℝ} (hx : L ≤ |x|) (y : ℝ) :
    f ((x : ℂ) + y * I) = 0 := by
  apply eq_zero_of_norm_ge_of_tsupport_in_ball h_supp
  rw [Complex.norm_add_mul_I]
  have h2 : |x| = Real.sqrt (x ^ 2) := by rw [Real.sqrt_sq_eq_abs]
  have h3 : Real.sqrt (x ^ 2) ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
    apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg y]
  linarith [h2 ▸ h3]

/-- Cut the outer `ℝ`-integral to `Ioc (-L) L`. -/
private lemma integral_real_eq_integral_Ioc_of_supp
    {f : ℂ → ℂ} {L : ℝ} (hL_pos : 0 < L)
    (h_supp : tsupport f ⊆ Metric.ball 0 L) :
    ∫ x : ℝ, ∫ y : ℝ, f ((x : ℂ) + y * I)
      = ∫ x in Set.Ioc (-L) L, ∫ y : ℝ, f ((x : ℂ) + y * I) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  -- `x ∉ Ioc (-L) L` means `x ≤ -L ∨ L < x`.
  have hx' : L ≤ |x| := by
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · -- `x ≤ -L`, so `x < 0`, so `|x| = -x ≥ L`.
      have h_neg : x ≤ 0 := by linarith
      have h_abs : |x| = -x := abs_of_nonpos h_neg
      linarith
    · -- `L < x`, so `0 < x`, so `|x| = x > L`.
      have h_pos : 0 < x := by linarith
      have h_abs : |x| = x := abs_of_pos h_pos
      linarith
  have h_zero : ∀ y : ℝ, f ((x : ℂ) + y * I) = 0 := fun y =>
    inner_integrand_eq_zero_of_abs_re_ge h_supp hx' y
  simp_rw [h_zero, integral_zero]

/-- Cut the inner `ℝ`-integral (fixed `x`) to `Ioc (-L) L`. -/
private lemma inner_integral_real_eq_integral_Ioc_of_supp
    {f : ℂ → ℂ} {L : ℝ} (hL_pos : 0 < L)
    (h_supp : tsupport f ⊆ Metric.ball 0 L) (x : ℝ) :
    ∫ y : ℝ, f ((x : ℂ) + y * I)
      = ∫ y in Set.Ioc (-L) L, f ((x : ℂ) + y * I) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  apply eq_zero_of_norm_ge_of_tsupport_in_ball h_supp
  rw [Complex.norm_add_mul_I]
  have hy' : L ≤ |y| := by
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · have h_neg : y ≤ 0 := by linarith
      have h_abs : |y| = -y := abs_of_nonpos h_neg
      linarith
    · have h_pos : 0 < y := by linarith
      have h_abs : |y| = y := abs_of_pos h_pos
      linarith
  have h2 : |y| = Real.sqrt (y ^ 2) := by rw [Real.sqrt_sq_eq_abs]
  have h3 : Real.sqrt (y ^ 2) ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
    apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg x]
  linarith [h2 ▸ h3]

/-! ## Main bridge theorem -/

/-- **Bridge from iterated to plane integral (Chip 3c-E, Section A).**
For `f : ℂ → ℂ` integrable with `tsupport f ⊆ Metric.ball 0 L`,
```
∫ ζ : ℂ, f ζ = ∫ x in -L..L, ∫ y in -L..L, f ((x : ℂ) + y * I).
```

This converts the iterated-integral form of Chip 3c-D's balance
equation into the plane (Bochner-over-ℂ) form needed for the DCT
limit `ε → 0`. -/
theorem integral_complex_eq_iteratedIntegral_of_tsupport_in_ball
    {f : ℂ → ℂ} (h_int : Integrable f) {L : ℝ} (hL_pos : 0 < L)
    (h_supp : tsupport f ⊆ Metric.ball 0 L) :
    ∫ ζ : ℂ, f ζ
      = ∫ x in -L..L, ∫ y in -L..L, f ((x : ℂ) + y * I) := by
  rw [integral_complex_eq_integral_prod, integral_prod_eq_iterated h_int,
      integral_real_eq_integral_Ioc_of_supp hL_pos h_supp]
  -- Now: `∫ x in Ioc (-L) L, ∫ y : ℝ, f((x:ℂ) + y*I) = ∫ x in -L..L, ∫ y in -L..L, ...`.
  rw [intervalIntegral.integral_of_le (by linarith : (-L : ℝ) ≤ L)]
  congr 1
  funext x
  rw [inner_integral_real_eq_integral_Ioc_of_supp hL_pos h_supp x,
      intervalIntegral.integral_of_le (by linarith : (-L : ℝ) ≤ L)]

end JacobianChallenge.PompeiuKernel

end
