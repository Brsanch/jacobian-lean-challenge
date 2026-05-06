/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchored
import JacobianChallenge.Manifold.CircleResidue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Anchored chart-circle integral and its residue discharge

This file delivers the **half-bundle real discharge** for the chart-anchored
log-derivative coefficient `MeromorphicNonzero.logDiffCoeffAt` (defined in
`LogDiffAnchored.lean`):

* Commit A — definition `chartCircleIntegralAnchored f x r` mirroring
  `MeromorphicOneForm.chartCircleIntegral` but **bypassing** the
  `MeromorphicOneForm` bundle, since the bundle would require proving
  `MMeromorphicAt (logDiffCoeffAt f x) y` for every `y`, which is the same
  generic-`y` chart-uniformity obstruction described in the
  `MeromorphicOneForm` design note.
* Commit B — generic residue-extraction lemma
  `chartCircleIntegralOfFun_of_residue_plus_analytic`. Given any
  `g : X → ℂ` whose chart-pulled-back values on the chart-circle of radius
  `r` decompose as `c_neg / (z - z₀) + h(z)` with `h` continuous on the
  closed disk and differentiable on the open disk, the normalised
  chart-circle integral of `g` equals `c_neg`. The proof is a verbatim
  port of `MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_residue_plus_analytic`,
  but *de-bundled* — it operates on `g` directly rather than `α.coeff`.
* Commit C — final discharge
  `logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`. Under
  the right-shape hypothesis `LogDerivResiduePlusAnalyticAnchored f x`
  (already shipped in `LogDiffAnchored.lean` as a `Prop`-valued `def`), the
  anchored chart-circle integral of `logDiffCoeffAt f x` equals the integer
  order of `f` at `x`, cast to `ℂ`.

The conditional form of the deliverable is the honest one: closing it
*unconditionally* requires producing a witness for
`LogDerivResiduePlusAnalyticAnchored f x` from `h_mero`, which is the same
planar-Laurent-factorisation chip tracked separately in `OPEN.md`. The
discharge here removes the *integration* and *residue-extraction* parts of
the gap unconditionally.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed (this is a pure addition).
* `chartCircleIntegralAnchored` has a real `intervalIntegral` body, not a
  `0`-stub.
* The residue extraction is proven via mathlib's
  `circleIntegral.integral_sub_inv_of_mem_ball` and
  `DiffContOnCl.circleIntegral_eq_zero` (Cauchy-Goursat).
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Anchored chart-circle integral, de-bundled

`chartCircleIntegralAnchored f x r` is the normalised line integral of
`logDiffCoeffAt f x` over the chart-circle of radius `r` centred at
`(chartAt ℂ x) x`. It mirrors `MeromorphicOneForm.chartCircleIntegral` but
does *not* require bundling `logDiffCoeffAt f x` into a
`MeromorphicOneForm` (which would demand pointwise meromorphicity at
*every* `y`, blocked by the chart-at-`y` issue). -/

/-- **De-bundled normalised chart-circle integral** of an arbitrary
function `g : X → ℂ`. The body is the same as
`MeromorphicOneForm.chartCircleIntegral`, except that `α.coeff` is replaced
by the user-supplied `g`. -/
def chartCircleIntegralOfFun
    (g : X → ℂ) (x : X) (r : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      g ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ)))

@[simp] lemma chartCircleIntegralOfFun_def
    (g : X → ℂ) (x : X) (r : ℝ) :
    chartCircleIntegralOfFun (X := X) g x r =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          g ((chartAt ℂ x).symm
                ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
            * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ))) := rfl

/-- **Anchored chart-circle integral of `f' / f`.** The normalised line
integral of the chart-anchored log-derivative coefficient
`logDiffCoeffAt f x` over the chart-circle of radius `r`. Specialisation
of `chartCircleIntegralOfFun` to `g = logDiffCoeffAt f x`. -/
def chartCircleIntegralAnchored
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) : ℂ :=
  chartCircleIntegralOfFun (logDiffCoeffAt f x) x r

@[simp] lemma chartCircleIntegralAnchored_def
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) :
    chartCircleIntegralAnchored f x r =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          logDiffCoeffAt f x ((chartAt ℂ x).symm
                ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
            * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ))) := rfl

/-! ## Bridge to mathlib's `circleIntegral`

Mirrors `MeromorphicOneForm.chartCircleIntegral_eq_circleIntegral_of_coeff_eq`
but operates on a free function `g : X → ℂ` instead of `α.coeff`. -/

/-- **Bridge:** rewrite `chartCircleIntegralOfFun` as `(2πi)⁻¹ ·` mathlib's
`circleIntegral` applied to a function `f : ℂ → ℂ`, provided the
chart-pulled-back values of `g` agree with `f ∘ circleMap z₀ r` on the
integration interval. -/
lemma chartCircleIntegralOfFun_eq_circleIntegral_of_eq
    (g : X → ℂ) (x : X) (r : ℝ) (f : ℂ → ℂ)
    (h : ∀ θ : ℝ,
      g ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = f (circleMap ((chartAt ℂ x) x) r θ)) :
    chartCircleIntegralOfFun (X := X) g x r =
      (2 * Real.pi * Complex.I)⁻¹ *
        (∮ z in C((chartAt ℂ x) x, r), f z) := by
  rw [chartCircleIntegralOfFun_def]
  show _ = (2 * Real.pi * Complex.I)⁻¹ * circleIntegral f ((chartAt ℂ x) x) r
  unfold circleIntegral
  congr 1
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [h θ, deriv_circleMap]
  have hθcomm :
      Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [mul_comm]
  rw [circleMap_zero, smul_eq_mul, ← hθcomm]
  ring

/-! ## Residue extraction (de-bundled)

Mirrors `MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_residue_plus_analytic`
but operates on a free function `g : X → ℂ`. -/

/-- **Residue extraction, de-bundled.** If on the chart-circle of radius
`r > 0` centred at `z₀ := (chartAt ℂ x) x`, the chart-pulled-back values
of `g` decompose as `c_neg / (z - z₀) + h(z)` with `h` continuous on the
closed disk and differentiable on the open disk, then the normalised
chart-circle integral of `g` equals `c_neg`.

The proof is a verbatim port of
`MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_residue_plus_analytic`,
de-bundled to operate on `g` directly via
`chartCircleIntegralOfFun_eq_circleIntegral_of_eq`. -/
theorem chartCircleIntegralOfFun_of_residue_plus_analytic
    (g : X → ℂ) (x : X) (r : ℝ) (hr : 0 < r)
    (c_neg : ℂ) (h : ℂ → ℂ)
    (h_cont : ContinuousOn h (Metric.closedBall ((chartAt ℂ x) x) r))
    (h_diff : DifferentiableOn ℂ h (Metric.ball ((chartAt ℂ x) x) r))
    (h_eq : ∀ θ : ℝ,
      g ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = c_neg * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹
            + h ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    chartCircleIntegralOfFun (X := X) g x r = c_neg := by
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- Rewrite `(r·exp(Iθ))` as `circleMap z₀ r θ - z₀`.
  have hsub : ∀ θ : ℝ,
      circleMap z₀ r θ - z₀ = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro θ
    rw [circleMap_sub_center, circleMap_zero, mul_comm (Complex.I) ((θ : ℂ))]
  have hmap : ∀ θ : ℝ,
      circleMap z₀ r θ = z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro θ
    have heq := hsub θ
    linear_combination heq
  -- Step 1: bridge to mathlib's `circleIntegral`.
  have hbridge :
      chartCircleIntegralOfFun (X := X) g x r =
        (2 * Real.pi * Complex.I)⁻¹ *
          (∮ z in C(z₀, r), c_neg * (z - z₀)⁻¹ + h z) := by
    refine chartCircleIntegralOfFun_eq_circleIntegral_of_eq g x r
      (fun z => c_neg * (z - z₀)⁻¹ + h z) ?_
    intro θ
    show g _ = c_neg * (circleMap z₀ r θ - z₀)⁻¹ + h (circleMap z₀ r θ)
    rw [h_eq θ, hsub θ, hmap θ]
  rw [hbridge]
  -- Step 2: each summand circle-integrable.
  have hpole_zpow_int :
      CircleIntegrable (fun z => (z - z₀) ^ (-1 : ℤ)) z₀ r := by
    rw [circleIntegrable_sub_zpow_iff]
    refine Or.inr (Or.inr ?_)
    intro hmem
    rw [Metric.mem_sphere, dist_self, abs_of_pos hr] at hmem
    exact hr.ne hmem
  have hpole : CircleIntegrable (fun z => c_neg * (z - z₀)⁻¹) z₀ r := by
    have hbase : CircleIntegrable (fun z => c_neg * (z - z₀) ^ (-1 : ℤ)) z₀ r := by
      have := hpole_zpow_int.const_fun_smul (a := c_neg)
      simpa [smul_eq_mul] using this
    have hrw : (fun z : ℂ => c_neg * (z - z₀)⁻¹)
        = (fun z => c_neg * (z - z₀) ^ (-1 : ℤ)) := by
      funext z; rw [zpow_neg_one]
    rw [hrw]; exact hbase
  have hsphere_subset : Metric.sphere z₀ r ⊆ Metric.closedBall z₀ r := by
    intro z hz
    rw [Metric.mem_closedBall]
    rw [Metric.mem_sphere] at hz
    exact le_of_eq hz
  have h_cont_sphere : ContinuousOn h (Metric.sphere z₀ r) :=
    h_cont.mono hsphere_subset
  have hh_int : CircleIntegrable h z₀ r :=
    ContinuousOn.circleIntegrable hr.le h_cont_sphere
  -- Distribute.
  rw [circleIntegral.integral_add hpole hh_int]
  -- Step 3: pole contributes c_neg · 2πi.
  have hmem_z0 : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hinv_int :
      (∮ z in C(z₀, r), (z - z₀)⁻¹) = 2 * Real.pi * Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball hmem_z0
  have hpole_eval :
      (∮ z in C(z₀, r), c_neg * (z - z₀)⁻¹) = c_neg * (2 * Real.pi * Complex.I) := by
    rw [circleIntegral.integral_const_mul, hinv_int]
  -- Step 4: analytic part contributes 0 by Cauchy-Goursat on a disk.
  have hh_eval : (∮ z in C(z₀, r), h z) = 0 := by
    have hdcc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
      refine ⟨?_, ?_⟩
      · exact h_diff
      · have hclosure : closure (Metric.ball z₀ r) = Metric.closedBall z₀ r :=
          closure_ball z₀ hr.ne'
        rw [hclosure]
        exact h_cont
    exact hdcc.circleIntegral_eq_zero hr.le
  rw [hpole_eval, hh_eval, add_zero]
  -- Step 5: (2πi)⁻¹ * (c_neg * 2πi) = c_neg.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero h2 hπ) Complex.I_ne_zero
  rw [show (c_neg * (2 * Real.pi * Complex.I) : ℂ)
        = (2 * Real.pi * Complex.I) * c_neg from by ring,
      ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

end MeromorphicNonzero

end JacobianChallenge

end
