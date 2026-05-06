/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicOneForm
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chart-anchored log-derivative coefficient

The existing `MeromorphicNonzero.logDiffCoeff` (in `MeromorphicOneForm.lean`)
is defined using the chart **at the evaluation point `y`**:

  `logDiffCoeff f y = deriv (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) / f.toFun y`

This per-point chart structure is the right thing for declaring the 1-form
`logDiff f` as a `MeromorphicOneForm X`, but it is awkward when one wants
to compare with mathlib's *planar* Laurent factorization
`meromorphicOrderAt_eq_int_iff`, which lives entirely on a single fixed
disk in `ℂ` around a single basepoint `(chartAt ℂ x) x`.

This file introduces the **chart-anchored** variant `logDiffCoeffAt`, which
pulls back through the chart at the (fixed) residue basepoint `x`, not the
per-point chart at `y`:

  `logDiffCoeffAt f x y = deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) / f.toFun y`

This is a pure addition: no existing definition or signature is changed.
-/

noncomputable section

open scoped Manifold ContDiff
open Complex

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-- **Chart-anchored log-derivative coefficient.** Pulls back through the
chart at the *residue basepoint* `x` (fixed) rather than the per-point chart
at `y`. The numerator is `deriv (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)`,
i.e. the planar derivative on the chart `(chartAt ℂ x).target ⊆ ℂ` evaluated
at the chart image of `y`.

Compare with `MeromorphicNonzero.logDiffCoeff` in `MeromorphicOneForm.lean`,
which uses the chart at the evaluation point `y` instead of a fixed
basepoint `x`. -/
def logDiffCoeffAt (f : MeromorphicNonzero X) (x y : X) : ℂ :=
  deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) / f.toFun y

@[simp] lemma logDiffCoeffAt_def (f : MeromorphicNonzero X) (x y : X) :
    logDiffCoeffAt f x y =
      deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) / f.toFun y := rfl

/-- **Chart-source identity.** On the chart source at the residue basepoint
`x`, the chart-anchored coefficient `logDiffCoeffAt f x y` equals the planar
log-derivative of `f.toFun ∘ (chartAt ℂ x).symm` at `(chartAt ℂ x) y`.

This is `rfl` from the definition; it is recorded as a named lemma so that
downstream files can reference the identity directly without unfolding the
definition. The `y ∈ (chartAt ℂ x).source` premise is the `PartialHomeomorph`-
hygiene witness — the chart symm is only well-behaved on `target`, and
`(chartAt ℂ x) y ∈ target` follows from `y ∈ source`. -/
lemma logDiffCoeffAt_eq_planar_logDeriv (f : MeromorphicNonzero X) (x : X) :
    ∀ y ∈ (chartAt ℂ x).source,
      logDiffCoeffAt f x y =
        deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) / f.toFun y := by
  intro y _; rfl

/-- **Chart-circle parameterization** at the residue basepoint `x`. Sends a
radius `r : ℝ` and an angle `θ : ℝ` to the manifold point obtained by
moving in chart coordinates from the chart center `(chartAt ℂ x) x` along
the circle of radius `r`, then pulling back via the chart inverse. -/
def circleParameter (x : X) (r : ℝ) (θ : ℝ) : X :=
  (chartAt ℂ x).symm ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

@[simp] lemma circleParameter_def (x : X) (r θ : ℝ) :
    circleParameter (X := X) x r θ =
      (chartAt ℂ x).symm
        ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := rfl

/-- **Bridge from `circleParameter` to the planar log-derivative.** When the
chart-circle point `(chartAt ℂ x) x + r·exp(iθ)` lies in the chart target,
the chart-anchored coefficient at the corresponding manifold point unfolds
to the planar log-derivative of `f.toFun ∘ (chartAt ℂ x).symm` evaluated
*directly* at the planar point — no double-pullback hygiene cost.

The hypothesis `htgt` is the small-`r` witness: for the radii of interest
the chart-circle stays inside `(chartAt ℂ x).target`. This is automatic for
sufficiently small `r > 0` because the chart target is open and contains
the chart center. -/
lemma logDiffCoeffAt_circleParameter
    (f : MeromorphicNonzero X) (x : X) (r θ : ℝ)
    (htgt :
      (chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
        (chartAt ℂ x).target) :
    logDiffCoeffAt f x (circleParameter (X := X) x r θ) =
      deriv (f.toFun ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        f.toFun (circleParameter (X := X) x r θ) := by
  unfold logDiffCoeffAt circleParameter
  rw [(chartAt ℂ x).right_inv htgt]

/-! ## Right-shape Laurent hypothesis (anchored variant)

The existing `LogDerivLaurent.LogDerivResiduePlusAnalytic` (in
`LogDerivLaurentDischarge.lean`) is the right-shape simple-pole +
analytic-remainder hypothesis for the *per-point chart* `logDiffCoeff`.
Producing a witness for that predicate from mathlib's planar
`meromorphicOrderAt_eq_int_iff` requires bridging between
`(chartAt ℂ y) y` (varying chart at each `y` on the chart-circle) and
`(chartAt ℂ x) y` (fixed chart at the residue basepoint). This bridge
is a separate manifold-hygiene chip.

`LogDerivResiduePlusAnalyticAnchored` below is the *anchored* variant:
it is stated against the chart-anchored coefficient `logDiffCoeffAt f x`
directly. It is exactly the shape that mathlib's planar Laurent
factorization delivers — no manifold-hygiene bridging is required. -/

/-- **Anchored simple-pole + analytic-remainder Laurent hypothesis.**

Anchored variant of `LogDerivLaurent.LogDerivResiduePlusAnalytic`: there
exists a small radius `r > 0` and a function `h : ℂ → ℂ`, continuous on
the closed disk of radius `r` around `z₀ := (chartAt ℂ x) x` and
differentiable on the open disk, such that on the chart-circle of radius
`r`,

  `logDiffCoeffAt f x (circleParameter x r θ)
     = (k : ℂ) * (r·exp(Iθ))⁻¹ + h (z₀ + r·exp(Iθ))`,

where `k` is the integer order
`(MMeromorphicOn.orderFun 𝓘(ℂ,ℂ) f.toFun x : ℤ)` cast to `ℂ`.

This is the **right** Laurent shape: at a meromorphic point of order
`k : ℤ`, the planar factorization `f̃(z) = (z - z₀)^k · g(z)` of
`f̃ := f.toFun ∘ (chartAt ℂ x).symm` (delivered by mathlib's
`meromorphicOrderAt_eq_int_iff` once `f̃` is shown meromorphic at `z₀`)
yields `f̃' / f̃ = k/(z - z₀) + g'/g` with `g'/g` analytic on a small
disk. The chart-anchored coefficient `logDiffCoeffAt f x y` is, by
definition, `(f̃)' (chart y) / f y`, so on the chart-circle it has
*exactly* this Laurent shape — no double-pullback bridging is needed.

Stated as a `Prop`-valued `def` (NOT `axiom`). Producing a witness from
mathlib is the next chip; this file ships the precise statement. -/
def LogDerivResiduePlusAnalyticAnchored
    (f : MeromorphicNonzero X) (x : X) : Prop :=
  ∃ (r : ℝ) (_hr : 0 < r) (h : ℂ → ℂ),
    ContinuousOn h (Metric.closedBall ((chartAt ℂ x) x) r) ∧
    DifferentiableOn ℂ h (Metric.ball ((chartAt ℂ x) x) r) ∧
    (∀ θ : ℝ,
      (chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
        (chartAt ℂ x).target) ∧
    ∀ θ : ℝ,
      logDiffCoeffAt f x (circleParameter (X := X) x r θ) =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ)
            * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹
          + h ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

end MeromorphicNonzero

end JacobianChallenge

end
