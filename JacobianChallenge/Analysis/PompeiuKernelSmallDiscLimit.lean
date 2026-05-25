/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import JacobianChallenge.Analysis.PompeiuKernel

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3a: small-disc circle-integral limit

This file proves the local small-disc limit underlying the
Cauchy-Pompeiu identity `∂̄(pompeiuKernel α) = α`:

```
lim_{ε → 0⁺} ∮_{|ζ - z| = ε} α ζ · (ζ - z)⁻¹ dζ = 2πi · α z
```

for any continuous `α : ℂ → ℂ`. This is the standard Cauchy-integral
limit at the singularity; the compact-support hypothesis on `α` is
*not* needed for this local step (it enters Chip 3b at the
large-rectangle boundary).

## Chip 3 arc context

* **Chip 3a (this file)** — small-disc limit:
    `Tendsto (∮_{C(z,ε)} α(ζ)·(ζ-z)⁻¹) (𝓝[>] 0) (𝓝 (2πi · α z))`.
* Chip 3b — rectangle Stokes applied to `α(ζ)/(ζ-z)` on
  `R := [−L, L]² \ closedBall z ε`, with the large-rectangle boundary
  contribution vanishing by compact support of `α`.
* Chip 3c — combine and take `ε → 0` to conclude
  `partialZBar (pompeiuKernel α) z = α z`.

## Main results

* `circleIntegrable_smul_inv_sub_of_continuous` — circle integrability
  of `ζ ↦ α ζ · (ζ - z)⁻¹` on `C(z, ε)` for continuous `α` and `ε > 0`.
* `circleIntegral_constant_smul_sub_inv` — the constant-coefficient
  computation `∮_{C(z, ε)} α z · (ζ - z)⁻¹ dζ = α z · (2πi)`.
* `norm_circleIntegral_remainder_le` — modulus-of-continuity bound on
  the remainder `∮_{C(z, ε)} (α ζ - α z) · (ζ - z)⁻¹`.
* `tendsto_circleIntegral_pompeiu_smallDisc` — the main theorem.

## Proof outline

For `ε > 0`, the integrand splits pointwise as
```
α ζ · (ζ - z)⁻¹ = α z · (ζ - z)⁻¹ + (α ζ - α z) · (ζ - z)⁻¹.
```
The first piece evaluates to `α z · 2πi` exactly via
`circleIntegral.integral_sub_inv_of_mem_ball`. The second piece is
bounded in norm by `2π · C` whenever `‖α ζ - α z‖ ≤ C` on the sphere,
via `circleIntegral.norm_integral_le_of_norm_le_const` applied to the
pointwise bound `‖(α ζ - α z) · (ζ - z)⁻¹‖ ≤ C / ε` on `sphere z ε`.
Continuity of `α` at `z` makes `C` arbitrarily small for `ε` small.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology

namespace JacobianChallenge.PompeiuKernel

variable {α : ℂ → ℂ} {z : ℂ}

/-! ## Circle integrability on the punctured small disc -/

/-- The Pompeiu integrand `ζ ↦ α ζ · (ζ - z)⁻¹` is circle-integrable on
`C(z, ε)` whenever `α` is continuous and `ε > 0`: the singularity at
`ζ = z` lies at the centre, not on the sphere. -/
lemma circleIntegrable_smul_inv_sub_of_continuous
    (h_cont : Continuous α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    CircleIntegrable (fun ζ : ℂ => α ζ * (ζ - z)⁻¹) z ε := by
  refine ContinuousOn.circleIntegrable hε.le ?_
  refine h_cont.continuousOn.mul ?_
  refine (continuous_id.sub continuous_const).continuousOn.inv₀ ?_
  intro ζ hζ
  have hζ_norm : ‖ζ - z‖ = ε := by
    have := mem_sphere_iff_norm.mp hζ
    simpa using this
  intro hzero
  have h : ζ - z = 0 := by simpa using hzero
  rw [h, norm_zero] at hζ_norm
  exact hε.ne' hζ_norm.symm

/-- The constant factor `α z · (ζ - z)⁻¹` is circle-integrable on
`C(z, ε)` for `ε > 0`. -/
lemma circleIntegrable_const_smul_inv_sub
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    CircleIntegrable (fun ζ : ℂ => α z * (ζ - z)⁻¹) z ε := by
  refine ContinuousOn.circleIntegrable hε.le ?_
  refine continuousOn_const.mul ?_
  refine (continuous_id.sub continuous_const).continuousOn.inv₀ ?_
  intro ζ hζ
  have hζ_norm : ‖ζ - z‖ = ε := by
    have := mem_sphere_iff_norm.mp hζ
    simpa using this
  intro hzero
  have h : ζ - z = 0 := by simpa using hzero
  rw [h, norm_zero] at hζ_norm
  exact hε.ne' hζ_norm.symm

/-- The remainder integrand `(α ζ - α z) · (ζ - z)⁻¹` is
circle-integrable on `C(z, ε)` for continuous `α` and `ε > 0`. -/
lemma circleIntegrable_remainder
    (h_cont : Continuous α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    CircleIntegrable (fun ζ : ℂ => (α ζ - α z) * (ζ - z)⁻¹) z ε := by
  refine ContinuousOn.circleIntegrable hε.le ?_
  refine (h_cont.continuousOn.sub continuousOn_const).mul ?_
  refine (continuous_id.sub continuous_const).continuousOn.inv₀ ?_
  intro ζ hζ
  have hζ_norm : ‖ζ - z‖ = ε := by
    have := mem_sphere_iff_norm.mp hζ
    simpa using this
  intro hzero
  have h : ζ - z = 0 := by simpa using hzero
  rw [h, norm_zero] at hζ_norm
  exact hε.ne' hζ_norm.symm

/-! ## Constant part: explicit Cauchy-integral computation -/

/-- The constant-coefficient piece of the small-disc Pompeiu integrand
integrates to `α z · 2πi` on `C(z, ε)` for any `ε > 0`. -/
lemma circleIntegral_constant_smul_sub_inv
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∮ ζ in C(z, ε), α z * (ζ - z)⁻¹) = α z * (2 * ↑π * I) := by
  rw [circleIntegral.integral_const_mul]
  congr 1
  exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hε)

/-! ## Remainder: modulus-of-continuity bound -/

/-- Norm bound on the remainder integral in terms of a uniform bound on
`‖α ζ - α z‖` over the sphere `sphere z ε`. The factor `(ζ - z)⁻¹` has
norm exactly `ε⁻¹` on the sphere, so the pointwise integrand is bounded
by `C / ε`, and `circleIntegral.norm_integral_le_of_norm_le_const`
multiplies by `2π · ε` to absorb the `ε`. -/
lemma norm_circleIntegral_remainder_le
    (α : ℂ → ℂ) (z : ℂ) {ε C : ℝ} (hε : 0 < ε)
    (hbound : ∀ ζ ∈ sphere z ε, ‖α ζ - α z‖ ≤ C) :
    ‖∮ ζ in C(z, ε), (α ζ - α z) * (ζ - z)⁻¹‖ ≤ 2 * π * C := by
  have hbd_pointwise : ∀ ζ ∈ sphere z ε,
      ‖(α ζ - α z) * (ζ - z)⁻¹‖ ≤ C / ε := by
    intro ζ hζ
    rw [norm_mul, norm_inv]
    have hζ_norm : ‖ζ - z‖ = ε := by
      have := mem_sphere_iff_norm.mp hζ
      simpa using this
    rw [hζ_norm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hbound ζ hζ) (inv_nonneg.mpr hε.le)
  have h := circleIntegral.norm_integral_le_of_norm_le_const
    (R := ε) (c := z) (f := fun ζ => (α ζ - α z) * (ζ - z)⁻¹)
    (C := C / ε) hε.le hbd_pointwise
  calc ‖∮ ζ in C(z, ε), (α ζ - α z) * (ζ - z)⁻¹‖
      ≤ 2 * π * ε * (C / ε) := h
    _ = 2 * π * C := by
        field_simp

/-! ## Decomposition lemma -/

/-- Pointwise decomposition `α ζ · (ζ - z)⁻¹ = α z · (ζ - z)⁻¹ +
(α ζ - α z) · (ζ - z)⁻¹`, lifted to circle integrals on `C(z, ε)` for
`ε > 0` (so all three pieces are circle integrable when `α` is
continuous). -/
lemma circleIntegral_pompeiu_decompose
    (h_cont : Continuous α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∮ ζ in C(z, ε), α ζ * (ζ - z)⁻¹)
      = (∮ ζ in C(z, ε), α z * (ζ - z)⁻¹)
        + (∮ ζ in C(z, ε), (α ζ - α z) * (ζ - z)⁻¹) := by
  have h_pointwise :
      (fun ζ : ℂ => α ζ * (ζ - z)⁻¹) =
        (fun ζ : ℂ => α z * (ζ - z)⁻¹ + (α ζ - α z) * (ζ - z)⁻¹) := by
    funext ζ
    ring
  rw [h_pointwise]
  exact circleIntegral.integral_add
    (circleIntegrable_const_smul_inv_sub α z hε)
    (circleIntegrable_remainder h_cont z hε)

/-! ## Main theorem -/

/-- **Small-disc Cauchy-integral limit (Chip 3a).** For any continuous
`α : ℂ → ℂ` and any `z : ℂ`,
```
lim_{ε → 0⁺} ∮_{|ζ - z| = ε} α ζ · (ζ - z)⁻¹ dζ = 2πi · α z.
```
This is the standard local Cauchy-integral identity at the singularity
of the Pompeiu kernel; it is the analytic content underlying Chip 3
(`∂̄(pompeiuKernel α) = α`) at the puncture `ζ = z`. The integral
splits into a constant `α z · 2πi` (exact via `integral_sub_inv_of_mem_ball`)
and a remainder controlled by the modulus of continuity of `α` at `z`. -/
theorem tendsto_circleIntegral_pompeiu_smallDisc
    (h_cont : Continuous α) (z : ℂ) :
    Tendsto (fun ε : ℝ => ∮ ζ in C(z, ε), α ζ * (ζ - z)⁻¹) (𝓝[>] 0)
      (𝓝 (α z * (2 * ↑π * I))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  -- Continuity at `z`: find `r > 0` with `‖ζ - z‖ < r → ‖α ζ - α z‖ < δ / (2π + 1)`.
  have hπ_nonneg : (0 : ℝ) ≤ 2 * π := by positivity
  set K : ℝ := δ / (2 * π + 1) with hK_def
  have hK_pos : 0 < K := by
    apply div_pos hδ
    have := Real.pi_pos
    linarith
  have hcont_z : ContinuousAt α z := h_cont.continuousAt
  rw [Metric.continuousAt_iff] at hcont_z
  obtain ⟨r, hr_pos, hr⟩ := hcont_z K hK_pos
  refine ⟨r, hr_pos, ?_⟩
  intro ε hε_mem hε_dist
  -- `hε_mem : ε ∈ Ioi 0`, `hε_dist : dist ε 0 < r`.
  have hε_pos : 0 < ε := hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_dist
  -- Bound `‖α ζ - α z‖ ≤ K` on `sphere z ε` from continuity.
  have hbound : ∀ ζ ∈ sphere z ε, ‖α ζ - α z‖ ≤ K := by
    intro ζ hζ
    have hζ_dist : dist ζ z = ε := by
      have := mem_sphere.mp hζ
      simpa using this
    have hζ_lt : dist ζ z < r := by rw [hζ_dist]; exact hε_dist
    have := (hr hζ_lt).le
    -- `this : dist (α ζ) (α z) ≤ K`
    simpa [dist_eq_norm] using this
  -- Decompose the integral.
  have h_split := circleIntegral_pompeiu_decompose h_cont z hε_pos
  have h_const := circleIntegral_constant_smul_sub_inv α z hε_pos
  have h_rem := norm_circleIntegral_remainder_le α z hε_pos hbound
  -- Compute the difference in `ℂ` and reduce `dist` to `‖·‖`.
  have hdiff_eq :
      (∮ ζ in C(z, ε), α ζ * (ζ - z)⁻¹) - α z * (2 * ↑π * I)
        = ∮ ζ in C(z, ε), (α ζ - α z) * (ζ - z)⁻¹ := by
    rw [h_split, h_const]
    ring
  rw [dist_eq_norm, hdiff_eq]
  calc ‖∮ ζ in C(z, ε), (α ζ - α z) * (ζ - z)⁻¹‖
      ≤ 2 * π * K := h_rem
    _ < (2 * π + 1) * K := by
        have hπ_pos := Real.pi_pos
        have : 2 * π < 2 * π + 1 := by linarith
        exact (mul_lt_mul_iff_of_pos_right hK_pos).mpr this
    _ = δ := by
        have h2π1_pos : 0 < 2 * π + 1 := by have := Real.pi_pos; linarith
        rw [hK_def]
        field_simp

end JacobianChallenge.PompeiuKernel
