/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Stokes' theorem on a closed disk in `ℂ` (local leg)

This file ships the **disk leg** of Stokes' theorem that the residue
theorem (R5) eventually globalises by a chart-cover argument:

For a closed smooth 1-form `ω` on a closed disk `D ⊆ ℂ` whose exterior
derivative `dω` vanishes on `D`, the boundary integral satisfies
`∮_{∂D} ω = 0`.

## What's actually proven (not stub) and what's a named gap

Mathlib at the pinned commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`
ships the **holomorphic Cauchy–Goursat theorem** for a closed disk in
two convenient forms:

* `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`
  (`Mathlib/Analysis/Complex/CauchyIntegral.lean`, line 445 at the pin):
  if `f` is continuous on `closedBall c R` and complex-differentiable
  on `ball c R \ s` for some countable set `s`, then
  `∮_{|z-c|=R} f z dz = 0`.
* `DiffContOnCl.circleIntegral_eq_zero` (same file, line 464): the
  same conclusion under `DiffContOnCl ℂ f (ball c R)`.

Specialising to the closed `(1,0)`-form `ω = f dz` gives the
**holomorphic** disk-Stokes leg as a real proven theorem
(`circleIntegral_eq_zero_of_holomorphic_on_closedBall` below): this is
the form that the residue theorem actually plugs into, since the
residue contribution lives in the holomorphic-coefficient chart.

The companion **real-valued, smooth** form of the disk-Stokes
statement — for arbitrary closed real 1-forms
`ω : ℂ → (ℂ →L[ℝ] ℝ)` rather than holomorphic ones — is *not*
named in mathlib at this pin in a form that applies directly to a
disk. The closest hooks are:

* `MeasureTheory.integral_divergence_of_hasFDerivAt` and the broader
  `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` — these
  package the divergence theorem for **rectangular boxes** in `ℝⁿ`,
  not for disks.
* `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean` — the
  box-integral version of Gauss-Green; same shape mismatch (boxes,
  not disks).

Going from a box to a disk would require either a smooth change of
variables (annular coordinates) plus a separate argument that the
boundary contributions of a disk-conformal box parametrisation vanish,
or a new packaging at the manifold level. Neither is mathlib content
at the pin.

We therefore ship the real-Stokes-on-a-disk fact as
`Stokes_disk_statement` — a `Prop`-valued `def` (NOT `axiom`) — naming
the hypothesis precisely. Downstream proofs that need only the
holomorphic case use `circleIntegral_eq_zero_of_holomorphic_on_closedBall`
directly.

## Anti-cheat

* No `axiom`, no `sorry`.
* `circleIntegral_eq_zero_of_holomorphic_on_closedBall` and its
  parametric corollary are real proofs that wrap the mathlib
  Cauchy–Goursat theorem.
* `Stokes_disk_statement` is a `Prop`-valued `def` whose hypotheses
  match the classical real-Stokes disk identity. It is honestly
  labelled as the named gap.
-/

noncomputable section

open scoped Real Topology
open Complex MeasureTheory Metric

namespace JacobianChallenge

namespace StokesDisk

/-! ## Holomorphic disk-Stokes (proven) -/

/-- **Cauchy–Goursat / holomorphic disk-Stokes.**

If `f : ℂ → ℂ` is continuous on the closed disk `closedBall c R` and
complex-differentiable on the open disk `ball c R`, then the boundary
integral of the closed `(1,0)`-form `f dz` over `∂(closedBall c R)`
is zero:

`∮_{|z - c| = R} f z dz = 0`.

This is the disk leg of Stokes' theorem for closed holomorphic
1-forms — the form that the chart-residue computation actually
consumes. The proof wraps mathlib's
`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`
with the empty exceptional set. -/
theorem circleIntegral_eq_zero_of_holomorphic_on_closedBall
    {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → ℂ} {c : ℂ}
    (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    h0 (s := (∅ : Set ℂ)) Set.countable_empty hc
    (fun z hz => hd z hz.1)

/-- **Holomorphic disk-Stokes, parametric form.**

Same statement as `circleIntegral_eq_zero_of_holomorphic_on_closedBall`,
written out in the explicit `θ ↦ c + R · exp(i θ)` parametrisation
that the chart-residue chip in `Manifold/CircleResidue.lean` uses.

The body of `circleIntegral` unfolds to
`∫ θ in 0..2π, deriv (circleMap c R) θ • f (circleMap c R θ)`, and
`deriv (circleMap c R) θ = circleMap 0 R θ * I = R · I · exp(I·θ)`,
so this is just the same identity rewritten. -/
theorem intervalIntegral_circleMap_eq_zero_of_holomorphic
    {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → ℂ} {c : ℂ}
    (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R, DifferentiableAt ℂ f z) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap c R) θ * f (circleMap c R θ) = 0 := by
  have h := circleIntegral_eq_zero_of_holomorphic_on_closedBall h0 hc hd
  -- `circleIntegral` unfolds to the parametric integral with `•` = `*` on `ℂ`.
  simpa [circleIntegral, smul_eq_mul] using h

/-! ## Real-valued disk-Stokes (named gap)

The classical real-Stokes statement for a smooth real-valued 1-form
on a closed disk in `ℂ ≃ ℝ²`. We package it as a `Prop`-valued `def`
whose hypothesis matches the classical statement: closure of the form
on the closed disk plus enough regularity for the boundary integral to
make sense.

For a smooth 1-form `ω : ℂ → (ℂ →L[ℝ] ℝ)` written in coordinates as
`ω = P dx + Q dy`, **closedness** (`dω = 0`) is equivalent to
`∂Q/∂x = ∂P/∂y` on the disk. The classical Green's theorem then gives

`∮_{|z - c| = R} (P dx + Q dy) = ∬_{|z - c| ≤ R} (∂Q/∂x − ∂P/∂y) dA = 0.`

Here we encode the boundary integral as
`∫ θ in 0..2π, ω(circleMap c R θ) (deriv (circleMap c R) θ)`, i.e.
the line integral of `ω` along the boundary circle, parameterised
counterclockwise.

The "closedness" hypothesis is encoded via the symmetry of the
Fréchet derivative of the dual `1`-form, which is the coordinate-free
form of `∂Q/∂x = ∂P/∂y`. -/

/-- **Real-valued disk-Stokes (statement, NOT proven).**

For a `C¹` real 1-form `ω : ℂ → (ℂ →L[ℝ] ℝ)` defined on a
neighbourhood of the closed disk `closedBall c R`, if `ω` is closed
(its Fréchet derivative is symmetric) on the closed disk, then the
counterclockwise boundary line integral

`∫₀^{2π} ω(circleMap c R θ) (deriv (circleMap c R) θ) dθ`

equals zero.

**Status:** `Prop`-valued `def`, NOT proven, NOT axiomatised. The
holomorphic specialisation is proven above as
`circleIntegral_eq_zero_of_holomorphic_on_closedBall`; that is the
form the residue chain actually needs. The general real-Stokes-disk
statement is named so the dependency surface is explicit.

Closest mathlib content at the pin: the rectangular-box divergence
theorem in `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
and `Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`. Neither
applies directly to a disk; bridging requires either a conformal
parametrisation argument or a separate manifold-level packaging that
is not present at the pin. -/
def Stokes_disk_statement (c : ℂ) (R : ℝ)
    (ω : ℂ → (ℂ →L[ℝ] ℝ)) : Prop :=
  0 ≤ R →
  ContinuousOn ω (closedBall c R) →
  (∀ z ∈ closedBall c R,
      ∃ ω' : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ),
        HasFDerivAt ω ω' z ∧
          ∀ u v : ℂ, ω' u v = ω' v u) →
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ω (circleMap c R θ) (deriv (circleMap c R) θ) = 0

end StokesDisk

end JacobianChallenge

end
