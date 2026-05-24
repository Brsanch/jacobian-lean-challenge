/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBar
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal

set_option linter.unusedSectionVars false

/-! # Chart-side CR-converse + Cauchy regularity bridge (Chip 2b)

This file ships the chart-side bridge from "smooth-real + `∂̄ = 0` on an
open set" to "analytic on that open set". This is the **classical
Cauchy regularity theorem** in the form needed for Chip 2c (the
Forster §16.9 cutoff + correction discharge of `hSP X`):

* the inner-ball part of the construction needs `u : X → ℂ` to be
  analytic at the pole point `p`, which we obtain from `∂̄ u = 0` on
  the inner ball (because the compactly-supported source `α` of the
  ∂̄-equation vanishes there);
* the off-pole part needs `f = g₀ − u` to be analytic at every
  `x ≠ p`, which we obtain from `∂̄ (g₀ − u) = α − α = 0` off `p`.

Both reductions go through this file's chart-side CR-converse → Cauchy
regularity bridge.

## What this file ships

* `differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero`
  — pointwise CR-converse: ℝ-differentiable + `partialZBar f z = 0`
  ⇒ ℂ-differentiable at `z`. Wraps mathlib's
  `differentiableAt_complex_iff_differentiableAt_real`.
* `analyticOnNhd_of_contDiffOn_of_partialZBar_eqOn_zero` — bridge:
  `f : ℂ → ℂ` `C^∞-ℝ` on open `U` + `partialZBar f` vanishes on `U`
  ⇒ `AnalyticOnNhd ℂ f U`. Composes the pointwise CR-converse with
  mathlib's `DifferentiableOn.analyticOnNhd` (Cauchy regularity).
* `analyticAt_of_contDiffOn_of_partialZBar_eqOn_zero` — the same,
  shipped as the `AnalyticAt` corollary for direct consumption by
  Chip 2c at the pole / off-pole points.

These are the chart-side `ℂ → ℂ` building blocks. Chip 2c will route
the manifold-side discharges through them via the canonical chart
pullback. The bridge is sorry / axiom free.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology
open Complex

namespace JacobianChallenge

/-! ## Chart-side CR-converse helpers (ℂ → ℂ; no manifold yet) -/

section CRConverse

/-- **Cauchy-Riemann equation from `partialZBar = 0`.** The
chart-side computation that turns vanishing of the Wirtinger
antiholomorphic derivative into the canonical CR identity
`fderiv ℝ f z I = I • fderiv ℝ f z 1` consumed by mathlib's
`differentiableAt_complex_iff_differentiableAt_real`. -/
private lemma fderivR_I_eq_I_fderivR_one_of_partialZBar_zero
    {f : ℂ → ℂ} {z : ℂ} (h : partialZBar f z = 0) :
    fderiv ℝ f z I = I • fderiv ℝ f z 1 := by
  unfold partialZBar at h
  -- `h : (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + I * fderiv ℝ f z I) = 0`
  have h_inv : ((2 : ℂ)⁻¹) ≠ 0 := by norm_num
  have h_sum : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 :=
    (mul_eq_zero.mp h).resolve_left h_inv
  show fderiv ℝ f z I = I * fderiv ℝ f z 1
  have hI2 : I * I = -1 := Complex.I_mul_I
  linear_combination (-I) * h_sum + fderiv ℝ f z I * hI2

/-- **Chart-side CR-converse (pointwise).** If `f : ℂ → ℂ` is
real-differentiable at `z` and `partialZBar f z = 0`, then `f` is
complex-differentiable at `z`. -/
lemma differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero
    {f : ℂ → ℂ} {z : ℂ}
    (hR : DifferentiableAt ℝ f z) (h_dbar : partialZBar f z = 0) :
    DifferentiableAt ℂ f z := by
  refine differentiableAt_complex_iff_differentiableAt_real.mpr ⟨hR, ?_⟩
  exact fderivR_I_eq_I_fderivR_one_of_partialZBar_zero h_dbar

/-- **Chart-side CR-converse on an open set ⇒ AnalyticOnNhd.** If `f` is
`C^∞-ℝ` on an open set `U` and `partialZBar f y = 0` for all `y ∈ U`,
then `f` is analytic in a neighborhood of every point of `U`. -/
lemma analyticOnNhd_of_contDiffOn_of_partialZBar_eqOn_zero
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ⊤ f U)
    (h_dbar : ∀ y ∈ U, partialZBar f y = 0) :
    AnalyticOnNhd ℂ f U := by
  -- First: `DifferentiableOn ℂ f U`.
  have h_diff_C : DifferentiableOn ℂ f U := by
    intro z hz
    have h_diff_R_on : DifferentiableOn ℝ f U :=
      hf.differentiableOn (by decide)
    have h_diff_R_at : DifferentiableAt ℝ f z :=
      (h_diff_R_on z hz).differentiableAt (hU.mem_nhds hz)
    exact (differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero
        h_diff_R_at (h_dbar z hz)).differentiableWithinAt
  -- Apply mathlib's `DifferentiableOn.analyticOnNhd` for open `U`.
  exact h_diff_C.analyticOnNhd hU

/-- **Pointwise form of the CR converse → AnalyticAt.** -/
lemma analyticAt_of_contDiffOn_of_partialZBar_eqOn_zero
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ⊤ f U)
    (h_dbar : ∀ y ∈ U, partialZBar f y = 0)
    {z : ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z :=
  analyticOnNhd_of_contDiffOn_of_partialZBar_eqOn_zero hU hf h_dbar z hz

end CRConverse

end JacobianChallenge

end
