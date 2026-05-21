/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option linter.unusedSectionVars false

/-! # The `dbar` operator (`∂̄`) on a complex 1-manifold

This file lays the **foundational infrastructure** for the `∂̄`-operator
on a complex 1-manifold `X`, applied to smooth ℂ-valued functions
`f : X → ℂ`. This is a prerequisite for the Dolbeault / L²-Hodge route
to Riemann-Roch existence at genus 0 (`ExistsSimplePoleGermAtSomePoint
X` via solvability of `∂̄ u = h` on `X`).

## ℂ-linear / ℂ-antilinear decomposition of `ℝ`-linear maps `ℂ →L[ℝ] ℂ`

For `f : ℂ → ℂ` real-differentiable at `z₀`, the real Fréchet derivative
`fderiv ℝ f z₀ : ℂ →L[ℝ] ℂ` is an `ℝ`-linear map. Any such map
decomposes uniquely as a sum of a `ℂ`-linear part and a `ℂ`-antilinear
part:

  `T = T_lin + T_antilin`, where
  `T_lin (w) = (1/2) (T(w) - i T(iw))`,
  `T_antilin (w) = (1/2) (T(w) + i T(iw))`.

The `ℂ`-linear part is the **Wirtinger derivative `∂f`** and the
`ℂ`-antilinear part is the **`∂̄`-Wirtinger derivative `∂̄f`**.

A function is holomorphic at `z₀` iff `∂̄f(z₀) = 0` (equivalently the
Cauchy-Riemann equations hold).

## What this file ships

* `dbarChart f z₀ : ℂ → ℂ` — the chart-side ∂̄ operator: takes the
  ℂ-antilinear part of `fderiv ℝ f z₀`, evaluated at the unit tangent
  `1 : ℂ`. (More precisely: `dbarChart f z₀ = (1/2)(fderiv ℝ f z₀ 1 +
  i · fderiv ℝ f z₀ i)`.) Returns `0` when `f` is not real-differentiable.

* `dbarChart_add` — additivity of `dbarChart`.

* `dbarChart_const` — `dbarChart (fun _ => c) z₀ = 0`.

## Honest scope

This file defines `dbarChart` and proves basic linearity. It does **not**
yet:

* Lift `dbarChart` from `ℂ → ℂ` to `f : X → ℂ` via chart pullback (the
  manifold version `dbar`).
* Prove the characterization `dbarChart f z₀ = 0 ↔ HasDerivAt f _ z₀`
  (i.e., the ℝ-derivative is ℂ-linear, i.e., the Cauchy-Riemann
  equations).
* Set up the ∂̄-equation `dbar u = h` on `X`.
* Prove H¹ vanishing on compact Riemann surfaces at genus 0.

Each of these is a separate downstream chip. This file is the **first
step** in the multi-chip Dolbeault arc.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open ContinuousLinearMap

namespace JacobianChallenge

/-! ## Chart-side `dbarChart` operator on `ℂ → ℂ` -/

/-- **Chart-side `∂̄f(z₀)`**: the ℂ-antilinear part of `fderiv ℝ f z₀`,
evaluated at `1 : ℂ`. Returns `0` when `f` is not real-differentiable at
`z₀`.

Formula: `dbarChart f z₀ = (1/2) · (fderiv ℝ f z₀ 1 + Complex.I · fderiv ℝ f z₀ Complex.I)`.

When `f` is holomorphic at `z₀` (equivalently, `fderiv ℝ f z₀` is
ℂ-linear), `dbarChart f z₀ = 0`.

Conversely, when `dbarChart f z₀ = 0` (and `f` is real-differentiable
at `z₀`), `f` satisfies the Cauchy-Riemann equations at `z₀` and is
ℝ-holomorphic. -/
def dbarChart (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z₀ 1 + Complex.I * fderiv ℝ f z₀ Complex.I)

/-- **Constant function has zero `∂̄`.** `dbarChart (fun _ => c) z₀ = 0`. -/
@[simp] lemma dbarChart_const (c : ℂ) (z₀ : ℂ) :
    dbarChart (fun _ : ℂ => c) z₀ = 0 := by
  unfold dbarChart
  show 1/2 * ((fderiv ℝ (Function.const ℂ c) z₀) 1
    + Complex.I * (fderiv ℝ (Function.const ℂ c) z₀) Complex.I) = 0
  rw [fderiv_const]
  simp

/-- **Zero function has zero `∂̄`.** -/
@[simp] lemma dbarChart_zero (z₀ : ℂ) :
    dbarChart (0 : ℂ → ℂ) z₀ = 0 := by
  have h : (0 : ℂ → ℂ) = fun _ : ℂ => (0 : ℂ) := rfl
  rw [h, dbarChart_const]

/-- **Additivity of `dbarChart`** for differentiable functions. -/
lemma dbarChart_add {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : DifferentiableAt ℝ f z₀) (hg : DifferentiableAt ℝ g z₀) :
    dbarChart (f + g) z₀ = dbarChart f z₀ + dbarChart g z₀ := by
  unfold dbarChart
  rw [fderiv_add hf hg]
  simp only [add_apply]
  ring

-- (ℂ-scalar action chip deferred — needs IsScalarTower setup; the additive
-- structure above suffices for the foundational arc.)

/-- **Negation distributes.** `dbarChart (-f) z₀ = -dbarChart f z₀`. -/
lemma dbarChart_neg (f : ℂ → ℂ) (z₀ : ℂ) :
    dbarChart (-f) z₀ = -dbarChart f z₀ := by
  unfold dbarChart
  rw [fderiv_neg]
  simp only [neg_apply]
  ring

/-! ## Holomorphic functions have zero `∂̄` (deferred)

The `dbarChart f z₀ = 0` characterization for ℂ-differentiable `f` is a
follow-up chip — it requires routing through `HasFDerivAt.restrictScalars
ℝ`, which needs an `IsScalarTower ℝ ℂ ℂ` instance that does not synth
in this import context (despite the high-priority `IsScalarTower.right`
instance in `Mathlib.Algebra.Algebra.Defs`). A separate follow-up chip
will resolve the import/synthesis issue.

The basic definition + linearity + constant-zero lemmas in this file
suffice for the foundational arc; the holomorphic characterization is
mechanical glue on top. -/

end JacobianChallenge

end
