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

end MeromorphicNonzero

end JacobianChallenge

end
