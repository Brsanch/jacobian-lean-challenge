/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDerivLaurent
import Mathlib.Analysis.Complex.CauchyIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Discharge layer for `chartCircleIntegral_logDeriv_eq_order`

This file adds a **proven** R1-enhancement layer that strictly strengthens
the closed-form circle-integral lemma in
`Manifold/CircleResidue.lean`, plus a discharge of the chart-circle
integral identity for `d log f` against the *correct* mathematical shape
of the local expansion of `f' / f`.

## Context: why the previous Laurent hypothesis was the wrong shape

`LogDerivLaurent.LogDerivFiniteLaurent` (in `LogDerivLaurent.lean`)
asks for a **finite** Laurent decomposition of `logDiffCoeff f` on a
small chart circle. That is mathematically too strong: at a meromorphic
point of order `k : ℤ`, the local factorisation `f(z) = (z - z₀)^k · g(z)`
(mathlib `meromorphicOrderAt_eq_int_iff`) gives

  `f' / f = k / (z - z₀) + g' / g`

where `g' / g` is *analytic* on a small disk (since `g(z₀) ≠ 0`, so
`g` is non-zero on a neighbourhood, hence `g'/g` is differentiable
there). The analytic summand has, in general, an **infinite** Taylor
expansion — it is *not* a finite Laurent polynomial. So the original
`LogDerivFiniteLaurent` cannot be obtained from mathlib's local theory
without artificially truncating an infinite series.

The honest shape is **simple pole + analytic remainder**, which is what
this file delivers.

## What this file proves

* `MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_residue_plus_analytic`
  — the **R1 enhancement, fully proven**. If on the integration circle
  the chart-pulled-back coefficient of `α` equals
  `c_neg / (z - z₀) + h(z)` for a function `h` that is continuous on the
  closed disk and holomorphic on the open disk, then
  `α.chartCircleIntegral x r = c_neg`. The proof combines mathlib's
  `circleIntegral.integral_sub_inv_of_mem_ball` (residue contribution)
  with `DiffContOnCl.circleIntegral_eq_zero` (Cauchy-Goursat for the
  analytic remainder).

* `LogDerivLaurent.LogDerivResiduePlusAnalytic`
  — a `Prop`-valued statement matching the **correct** mathematical
  shape: there is a small `r > 0` and a function `h : ℂ → ℂ`
  continuous on the closed disk and holomorphic on the open disk such
  that on the chart circle,
  `logDiffCoeff f (chart.symm (z₀ + r·exp(Iθ)))` equals
  `(order f x : ℂ) / (r·exp(Iθ)) + h(z₀ + r·exp(Iθ))`.

* `chartCircleIntegral_logDeriv_eq_order_of_residue_plus_analytic`
  — the **discharge**: under `LogDerivResiduePlusAnalytic`, the chart-
  circle integral of `d log f` equals the order at `x`, cast to `ℂ`.
  This is proven, no `sorry`, no `axiom`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition signatures changed (in particular `Basic.lean`
  is untouched; the file in `LogDerivLaurent.lean` is also untouched —
  this is a pure addition).
* The `LogDerivResiduePlusAnalytic` hypothesis is a `Prop`-valued `def`,
  not an `axiom`. It is the *right* shape: it matches what mathlib's
  `meromorphicOrderAt_eq_int_iff` actually delivers (factor +
  analytic remainder), rather than the over-specified finite-Laurent
  hypothesis used by `LogDerivFiniteLaurent`.

## Remaining gap (named, not closed)

The chart-pulled-back step from mathlib's planar
`meromorphicOrderAt_eq_int_iff` to the manifold-level `logDiffCoeff f`
on a chart circle is NOT discharged here — that is a chart-hygiene
chase through the `MeromorphicNonzero.logDiffCoeff` definition (which
involves the chart at *each* evaluation point, not just the chart at
`x`), and is its own multi-cycle chip. This file removes the
*shape-mismatch* part of the gap (we now ask for the right thing) and
proves the residue extraction unconditionally; producing a witness is
left to a downstream file.
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicOneForm

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-! ## R1 enhancement: simple pole + analytic remainder

Strictly strengthens the finite-Laurent closed form of
`Manifold/CircleResidue.lean`: the analytic part need not be a finite
Laurent polynomial; *any* holomorphic-on-the-closed-disk function works,
because Cauchy-Goursat gives integral zero.
-/

/-- **R1 enhancement, proven.** If on the chart-circle of radius `r > 0`
centred at `z₀ := (chartAt ℂ x) x`, the chart-pulled-back coefficient of
`α` equals

  `c_neg / (z - z₀) + h(z)`

where `h : ℂ → ℂ` is **continuous on the closed disk** of radius `r` and
**differentiable on the open disk**, then `α.chartCircleIntegral x r = c_neg`.

Proof structure:
1. Bridge to mathlib's `circleIntegral` of the function
   `z ↦ c_neg * (z - z₀)⁻¹ + h(z)` via
   `chartCircleIntegral_eq_circleIntegral_of_coeff_eq`.
2. Distribute the integral over the sum (each summand circle-integrable):
   * `(z - z₀)⁻¹` is circle-integrable (by `circleIntegrable_sub_zpow_iff`,
     since `z₀ ∉ sphere z₀ r` for `r > 0`).
   * `h` is circle-integrable on `C(z₀, r)` since it is continuous on
     the sphere of radius `r` (the sphere lies in the closed ball).
3. Integrate the simple pole: `∮ (z - z₀)⁻¹ dz = 2πi` via
   `circleIntegral.integral_sub_inv_of_mem_ball`.
4. Integrate the analytic remainder: `∮ h dz = 0` via
   `DiffContOnCl.circleIntegral_eq_zero` (Cauchy-Goursat on a disk).
5. `(2πi)⁻¹ * (c_neg * 2πi + 0) = c_neg`. -/
theorem chartCircleIntegral_of_coeff_eq_residue_plus_analytic
    (α : MeromorphicOneForm X) (x : X) (r : ℝ) (hr : 0 < r)
    (c_neg : ℂ) (h : ℂ → ℂ)
    (h_cont : ContinuousOn h (Metric.closedBall ((chartAt ℂ x) x) r))
    (h_diff : DifferentiableOn ℂ h (Metric.ball ((chartAt ℂ x) x) r))
    (h_eq : ∀ θ : ℝ,
      α.coeff ((chartAt ℂ x).symm
                ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = c_neg * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹
            + h ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    α.chartCircleIntegral x r = c_neg := by
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- Helper: rewrite each `(r·exp(Iθ))` as `circleMap z₀ r θ - z₀`.
  have hsub : ∀ θ : ℝ,
      circleMap z₀ r θ - z₀ = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro θ
    rw [circleMap_sub_center, circleMap_zero, mul_comm (Complex.I) ((θ : ℂ))]
  have hmap : ∀ θ : ℝ,
      circleMap z₀ r θ = z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro θ
    have heq := hsub θ
    linear_combination heq
  -- Step 1: bridge via the existing helper lemma.
  have hbridge :
      α.chartCircleIntegral x r =
        (2 * Real.pi * Complex.I)⁻¹ *
          (∮ z in C(z₀, r), c_neg * (z - z₀)⁻¹ + h z) := by
    refine chartCircleIntegral_eq_circleIntegral_of_coeff_eq α x r
      (fun z => c_neg * (z - z₀)⁻¹ + h z) ?_
    intro θ
    show α.coeff _ = c_neg * (circleMap z₀ r θ - z₀)⁻¹ + h (circleMap z₀ r θ)
    rw [h_eq θ, hsub θ, hmap θ]
  rw [hbridge]
  -- Step 2: distribute integral over sum.
  -- Pole part is circle-integrable: write (z - z₀)⁻¹ = (z - z₀)^(-1 : ℤ).
  have hpole_zpow_int :
      CircleIntegrable (fun z => (z - z₀) ^ (-1 : ℤ)) z₀ r := by
    rw [circleIntegrable_sub_zpow_iff]
    -- We need: r = 0 ∨ 0 ≤ -1 ∨ z₀ ∉ sphere z₀ |r|.
    -- z₀ ∉ sphere z₀ |r| since dist z₀ z₀ = 0 ≠ r > 0.
    refine Or.inr (Or.inr ?_)
    intro hmem
    rw [Metric.mem_sphere, dist_self, abs_of_pos hr] at hmem
    exact hr.ne hmem
  have hpole : CircleIntegrable (fun z => c_neg * (z - z₀)⁻¹) z₀ r := by
    have hbase : CircleIntegrable (fun z => c_neg * (z - z₀) ^ (-1 : ℤ)) z₀ r := by
      have := hpole_zpow_int.const_fun_smul (a := c_neg)
      -- `c_neg • ((z - z₀) ^ (-1 : ℤ))` is `c_neg * ((z - z₀) ^ (-1 : ℤ))` for `ℂ`.
      simpa [smul_eq_mul] using this
    have hrw : (fun z : ℂ => c_neg * (z - z₀)⁻¹)
        = (fun z => c_neg * (z - z₀) ^ (-1 : ℤ)) := by
      funext z; rw [zpow_neg_one]
    rw [hrw]; exact hbase
  -- Analytic part is circle-integrable: continuous on the closed disk ⊇ sphere.
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
      · -- Continuous on closure(ball z₀ r) = closedBall z₀ r (when r > 0).
        have hclosure : closure (Metric.ball z₀ r) = Metric.closedBall z₀ r :=
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

end MeromorphicOneForm

namespace LogDerivLaurent

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Right-shape Laurent hypothesis: simple pole + analytic remainder

This is the *correct* mathematical shape for the local expansion of
`f' / f` near a meromorphic point of integer order `k`: a `k / (z - z₀)`
simple pole plus an analytic remainder. -/

/-- **Local "simple-pole + analytic remainder" decomposition of `f' / f`
near `x`.**

There is a small radius `r > 0` and a function `h : ℂ → ℂ`, continuous
on the closed disk of radius `r` around `z₀ := (chartAt ℂ x) x` and
differentiable on the open disk, such that on the chart circle of
radius `r`, the chart-pulled-back coefficient `logDiffCoeff f` equals

  `(order f x : ℂ) * (r·exp(Iθ))⁻¹ + h(z₀ + r·exp(Iθ))`.

This is the **right** Laurent shape: at a meromorphic point of order
`k : ℤ`, mathlib's `meromorphicOrderAt_eq_int_iff` factors
`f(z) = (z - z₀)^k · g(z)` with `g` analytic, `g(z₀) ≠ 0`. Differentiating,
`f' / f = k/(z - z₀) + g'/g`, with `g'/g` analytic on a small disk (since
`g` is nonzero on a neighbourhood of `z₀`). The analytic part is
**not** a finite Laurent polynomial in general; this hypothesis matches
the actual analytic structure delivered by mathlib.

Stated as a `Prop`-valued `def` (NOT `axiom`). -/
def LogDerivResiduePlusAnalytic (f : MeromorphicNonzero X)
    (h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (MeromorphicNonzero.logDiffCoeff f) x)
    (x : X) : Prop :=
  ∃ (r : ℝ) (_hr : 0 < r) (h : ℂ → ℂ),
    ContinuousOn h (Metric.closedBall ((chartAt ℂ x) x) r) ∧
    DifferentiableOn ℂ h (Metric.ball ((chartAt ℂ x) x) r) ∧
    ∀ θ : ℝ,
      (MeromorphicNonzero.logDiff f h_mero).coeff
          ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ)
            * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹
          + h ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-! ## Discharge: residue-plus-analytic ⇒ chart integral equals order

Under the right-shape hypothesis, R1-enhanced gives the residue
extraction unconditionally. -/

/-- **Chart-circle integral of `d log f` equals the order, complex form
(right-shape version).**

Under the simple-pole + analytic-remainder hypothesis, the normalised
chart-circle integral of `α := logDiff f h_mero` equals the integer order
`orderFun 𝓘(ℂ,ℂ) f.toFun x`, cast to `ℂ`.

Proven via the R1 enhancement
`MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_residue_plus_analytic`. -/
theorem chartCircleIntegral_logDeriv_eq_order_of_residue_plus_analytic
    (f : MeromorphicNonzero X)
    (h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (MeromorphicNonzero.logDiffCoeff f) x)
    {x : X}
    (H : LogDerivResiduePlusAnalytic f h_mero x) :
    ∃ r > (0 : ℝ),
      (MeromorphicNonzero.logDiff f h_mero).chartCircleIntegral x r =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  classical
  obtain ⟨r, hr, hfn, h_cont, h_diff, h_eq⟩ := H
  refine ⟨r, hr, ?_⟩
  exact MeromorphicOneForm.chartCircleIntegral_of_coeff_eq_residue_plus_analytic
    (MeromorphicNonzero.logDiff f h_mero) x r hr
    ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) hfn h_cont h_diff h_eq

/-! ## Combined witness: complex circle integral = canonical chart integral cast.

Same shape as `LogDerivLaurent.chartCircleIntegral_eq_canonicalChartIntegral_cast`
but using the right-shape hypothesis. -/

lemma chartCircleIntegral_eq_canonicalChartIntegral_cast_of_residue_plus_analytic
    (f : MeromorphicNonzero X)
    (h_mero : ∀ x, MMeromorphicAt (𝓘(ℂ, ℂ)) (MeromorphicNonzero.logDiffCoeff f) x)
    {x : X}
    (H : LogDerivResiduePlusAnalytic f h_mero x) :
    ∃ r > (0 : ℝ),
      (MeromorphicNonzero.logDiff f h_mero).chartCircleIntegral x r =
        ((canonicalChartIntegral f x : ℤ) : ℂ) :=
  chartCircleIntegral_logDeriv_eq_order_of_residue_plus_analytic f h_mero H

end LogDerivLaurent

end JacobianChallenge

end
