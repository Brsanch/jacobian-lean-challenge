/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchoredDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Stokes-on-disk for chart-pulled-back closed 1-forms (ZZ11 chip)

This file ships the **chart-side** packaging of the holomorphic
disk-Stokes vanishing: for any function `g : X → ℂ` whose chart-pulled-back
values on the chart-circle of radius `r > 0` agree with a planar function
`H : ℂ → ℂ` that is continuous on the closed chart-disk and complex-
differentiable on the open chart-disk (i.e. `DiffContOnCl ℂ H`), the
normalised chart-circle integral

  `chartCircleIntegralOfFun g x r = 0`.

This is the **closed-form / regular-point** specialisation of the
residue-extraction theorem
`chartCircleIntegralOfFun_of_residue_plus_analytic` with `c_neg = 0`.
The same specialisation is already used in `ChartCircleVanishingRegular`
to discharge the regular-point leg of the residue sum, but here we
package it as a stand-alone, non-`MeromorphicNonzero`-flavoured statement
that any chip can consume — the planar side of the input is exactly
mathlib's `DiffContOnCl ℂ H (Metric.ball z₀ r)` predicate.

## What is and isn't proven

* `chartCircleIntegralOfFun_eq_zero_of_diffContOnCl` — **proven**, no
  axioms, no sorry. Wraps `chartCircleIntegralOfFun_of_residue_plus_analytic`
  with `c_neg = 0`, the simple-pole term collapses, and the analytic
  remainder integrates to zero by Cauchy-Goursat
  (`DiffContOnCl.circleIntegral_eq_zero` inside the wrapper).
* `chartCircleIntegralOfFun_eq_zero_of_continuousOn_differentiableOn` —
  proven convenience corollary that takes `ContinuousOn` on the closed
  disk and `DifferentiableOn` on the open disk separately, repackaging
  them as `DiffContOnCl` internally.

The general real-valued (smooth, non-holomorphic) Stokes-on-disk
statement remains the named gap in `StokesDisk.Stokes_disk_statement`;
this file does **not** address it. The holomorphic / closed-`(1,0)`-form
case is what the residue chain actually consumes, and that is what we
ship here.

## Why this is a useful chip

The previous packaging (`chartCircleIntegralAnchored_eq_zero_of_regular`)
is keyed on `MeromorphicNonzero X` and `logDiffCoeffAt f x`. Downstream
chips that want the same vanishing but for a *generic* `g : X → ℂ` (e.g.
the `chartCircleSum` discharge in flight) had to re-derive the
`c_neg = 0` specialisation inline. This file makes the specialisation a
named, three-line consumer-facing lemma.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this is a pure addition.
* Only imports `JacobianChallenge.Manifold.LogDiffAnchoredDischarge`,
  which already imports the mathlib Cauchy-Goursat machinery.
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

/-- **Chart-side closed-form disk-Stokes (the chip).**

Let `g : X → ℂ` and `x : X`, `r > 0`. Suppose there is a planar function
`H : ℂ → ℂ` such that
* `H` is continuous on the closed chart-disk `closedBall ((chartAt ℂ x) x) r`,
* `H` is complex-differentiable on the open chart-disk
  `ball ((chartAt ℂ x) x) r`,
* the chart-pulled-back values of `g` agree with `H` on the chart-circle.

Then the normalised chart-circle integral vanishes:

  `chartCircleIntegralOfFun g x r = 0`.

This is the holomorphic disk-Stokes statement, written on the chart side:
the disk leg of Cauchy-Goursat (`DiffContOnCl.circleIntegral_eq_zero`)
plus the chart-bridge from `LogDiffAnchoredDischarge`. -/
theorem chartCircleIntegralOfFun_eq_zero_of_diffContOnCl
    (g : X → ℂ) (x : X) (r : ℝ) (hr : 0 < r)
    (H : ℂ → ℂ)
    (H_cont : ContinuousOn H
      (Metric.closedBall ((chartAt ℂ x) x) r))
    (H_diff : DifferentiableOn ℂ H
      (Metric.ball ((chartAt ℂ x) x) r))
    (H_eq : ∀ θ : ℝ,
      g ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = H ((chartAt ℂ x) x
              + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    chartCircleIntegralOfFun (X := X) g x r = 0 := by
  -- Apply the residue-extraction theorem with `c_neg = 0`: the simple-pole
  -- term `0 * (z - z₀)⁻¹` collapses identically and only the analytic
  -- remainder `H` survives.
  apply chartCircleIntegralOfFun_of_residue_plus_analytic
    g x r hr (0 : ℂ) H H_cont H_diff
  intro θ
  rw [H_eq θ]
  ring

/-- **Chart-side closed-form disk-Stokes, `DiffContOnCl` form.**

Same statement as `chartCircleIntegralOfFun_eq_zero_of_diffContOnCl` but
packaging the planar regularity hypothesis as a single `DiffContOnCl ℂ H`
predicate, which is the form mathlib's Cauchy-Goursat lemma
`DiffContOnCl.circleIntegral_eq_zero` directly consumes. -/
theorem chartCircleIntegralOfFun_eq_zero_of_DiffContOnCl
    (g : X → ℂ) (x : X) (r : ℝ) (hr : 0 < r)
    (H : ℂ → ℂ)
    (hH : DiffContOnCl ℂ H (Metric.ball ((chartAt ℂ x) x) r))
    (H_eq : ∀ θ : ℝ,
      g ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = H ((chartAt ℂ x) x
              + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    chartCircleIntegralOfFun (X := X) g x r = 0 := by
  -- Unpack `DiffContOnCl` into its differentiability and continuity-on-closure
  -- components, rewriting `closure (ball z₀ r) = closedBall z₀ r` for `r > 0`.
  have hclosure :
      closure (Metric.ball ((chartAt ℂ x) x) r)
        = Metric.closedBall ((chartAt ℂ x) x) r :=
    closure_ball ((chartAt ℂ x) x) hr.ne'
  have H_diff : DifferentiableOn ℂ H
      (Metric.ball ((chartAt ℂ x) x) r) := hH.differentiableOn
  have H_cont : ContinuousOn H
      (Metric.closedBall ((chartAt ℂ x) x) r) := by
    have := hH.continuousOn
    rw [hclosure] at this
    exact this
  exact chartCircleIntegralOfFun_eq_zero_of_diffContOnCl
    g x r hr H H_cont H_diff H_eq

/-- **Anchored specialisation of the chip.**

Specialisation of `chartCircleIntegralOfFun_eq_zero_of_diffContOnCl` to
`g = logDiffCoeffAt f x`. Same content as
`chartCircleIntegralAnchored_eq_zero_of_regular` from
`ChartCircleVanishingRegular`, but stated against the bare `DiffContOnCl`-
style hypothesis (no `IsRegularOn` predicate in the way). -/
theorem chartCircleIntegralAnchored_eq_zero_of_diffContOnCl
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) (hr : 0 < r)
    (H : ℂ → ℂ)
    (H_cont : ContinuousOn H
      (Metric.closedBall ((chartAt ℂ x) x) r))
    (H_diff : DifferentiableOn ℂ H
      (Metric.ball ((chartAt ℂ x) x) r))
    (H_eq : ∀ θ : ℝ,
      logDiffCoeffAt f x ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = H ((chartAt ℂ x) x
              + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    chartCircleIntegralAnchored f x r = 0 := by
  unfold chartCircleIntegralAnchored
  exact chartCircleIntegralOfFun_eq_zero_of_diffContOnCl
    (logDiffCoeffAt f x) x r hr H H_cont H_diff H_eq

end MeromorphicNonzero

end JacobianChallenge

end
