/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchoredDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chart-circle vanishing at regular points

Cauchy's theorem applied to `d log f`: when `f : MeromorphicNonzero X` is
holomorphic and nonzero on a chart-disk around `x`, the logarithmic
derivative `f' / f` is holomorphic on that disk, so its closed-curve
integral around the chart-circle vanishes.

In bundle terms: this is the chart-anchored circle integral
`chartCircleIntegralAnchored f x r`, defined in
`LogDiffAnchoredDischarge.lean`. The half-bundle real discharge already
produced there proves it equals `((order f x : ℤ) : ℂ)` under a
Laurent-shape hypothesis. At a regular point of order `0`, that integer
is `0`, but the present file does *not* go through the order witness:
it proves the vanishing **directly** from the regularity hypothesis,
phrased as "the chart-pulled-back values of `logDiffCoeffAt f x` agree
on the chart-circle with a function `H : ℂ → ℂ` that is continuous on
the closed disk and differentiable on the open disk".

The discharge is a mechanical specialisation of
`chartCircleIntegralOfFun_of_residue_plus_analytic` with `c_neg = 0`.

This is the **regular-point leg** of the global residue-sum identity:
points where `f` is holomorphic and nonzero contribute `0`, and only
the finite set of zeros and poles contribute.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this is a pure addition.
* The vanishing is proven via `chartCircleIntegralOfFun_of_residue_plus_analytic`
  and ultimately via mathlib's `DiffContOnCl.circleIntegral_eq_zero`
  (Cauchy-Goursat).

This commit (Z2B.A) ships only the predicate `IsRegularOn`. The
discharge `chartCircleIntegralAnchored_eq_zero_of_regular` lands in
commit Z2B.B once this file is CI-green.
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

/-! ## Regularity predicate

`IsRegularOn f x r` says that on the chart-circle of radius `r` around
the chart center `(chartAt ℂ x) x`, the chart-pulled-back values of
`logDiffCoeffAt f x` agree with a single planar function `H : ℂ → ℂ`
that is continuous on the *closed* disk of radius `r` and differentiable
on the *open* disk. This is the mathematical content of "the chart-disk
contains no zeros and no poles of `f`" — under that classical hypothesis,
`H` can be taken to be the planar logarithmic derivative
`(f̃)' / f̃` of `f̃ := f.toFun ∘ (chartAt ℂ x).symm`, which is holomorphic
on the disk because `f̃` is and `f̃` is nonzero there.

Stated as a `Prop`-valued `def` (not `axiom`). Producing a witness from
the classical "no zeros, no poles in the chart-disk" hypothesis is a
separate planar-holomorphicity chip; this file ships the precise
statement and (in commit Z2B.B) the unconditional discharge of the
*integration* leg. -/
def IsRegularOn
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) : Prop :=
  ∃ H : ℂ → ℂ,
    ContinuousOn H (Metric.closedBall ((chartAt ℂ x) x) r) ∧
    DifferentiableOn ℂ H (Metric.ball ((chartAt ℂ x) x) r) ∧
    ∀ θ : ℝ,
      logDiffCoeffAt f x ((chartAt ℂ x).symm
            ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = H ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-! ## Z2B.B — chart-circle vanishing at regular points

Cauchy's theorem applied to the chart-anchored log-derivative coefficient:
when `IsRegularOn f x r` holds (the chart-pulled-back values of
`logDiffCoeffAt f x` on the chart-circle agree with a planar function `H`
that is continuous on the closed disk and differentiable on the open
disk), the chart-anchored circle integral vanishes.

This is the **regular-point leg** of the global residue sum: at points
where `f` is holomorphic and nonzero, the chart-circle integral is `0`,
so only the finite zero/pole set contributes to the global sum.

The proof is a mechanical specialisation of
`chartCircleIntegralOfFun_of_residue_plus_analytic` with `c_neg = 0`:
the simple-pole term `c_neg / (z - z₀)` vanishes identically and the
analytic-remainder integrand `H` integrates to zero by Cauchy-Goursat
(`DiffContOnCl.circleIntegral_eq_zero` inside the Y1 wrapper). -/

theorem chartCircleIntegralAnchored_eq_zero_of_regular
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) (hr : 0 < r)
    (hreg : IsRegularOn f x r) :
    chartCircleIntegralAnchored f x r = 0 := by
  obtain ⟨H, H_cont, H_diff, H_eq⟩ := hreg
  unfold chartCircleIntegralAnchored
  apply chartCircleIntegralOfFun_of_residue_plus_analytic
    (logDiffCoeffAt f x) x r hr (0 : ℂ) H H_cont H_diff
  intro θ
  have heq := H_eq θ
  rw [heq]
  ring

end MeromorphicNonzero

end JacobianChallenge

end
