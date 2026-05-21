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
  change 1/2 * ((fderiv ℝ (Function.const ℂ c) z₀) 1
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

/-! ## Holomorphic functions have zero `∂̄`

Routes through mathlib's `HasDerivAt.complexToReal_fderiv`, which packages a
ℂ-derivative `HasDerivAt f f' z₀` as the ℝ-Fréchet derivative
`fderiv ℝ f z₀ = f' • (1 : ℂ →L[ℝ] ℂ)` (i.e. multiplication by `f'`).
Evaluating at `1` gives `f'`, at `i` gives `f' * i`; substituting into
the `dbarChart` formula gives `(1/2)·(f' + i·(f'·i)) = (1/2)·(f' - f') = 0`. -/

/-- **Holomorphic ⇒ `∂̄ = 0`.** If `f : ℂ → ℂ` is ℂ-differentiable at `z₀`
with derivative `f'`, then the chart-side `∂̄`-operator vanishes there. -/
theorem dbarChart_eq_zero_of_hasDerivAt {f : ℂ → ℂ} {z₀ f' : ℂ}
    (hf : HasDerivAt f f' z₀) : dbarChart f z₀ = 0 := by
  have h_fd : HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) z₀ :=
    hf.complexToReal_fderiv
  have h_fderiv : fderiv ℝ f z₀ = f' • (1 : ℂ →L[ℝ] ℂ) := h_fd.fderiv
  unfold dbarChart
  rw [h_fderiv]
  have h1 : (f' • (1 : ℂ →L[ℝ] ℂ)) 1 = f' := by
    change f' * 1 = f'
    ring
  have hI : (f' • (1 : ℂ →L[ℝ] ℂ)) Complex.I = f' * Complex.I := by
    change f' * Complex.I = f' * Complex.I
    rfl
  rw [h1, hI]
  -- Goal: (1/2) * (f' + I * (f' * I)) = 0
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ring_nf
  rw [show Complex.I^2 = Complex.I * Complex.I from sq Complex.I, hI2]
  ring

/-- **Holomorphic ⇒ `∂̄ = 0`**, stated with `DifferentiableAt ℂ`. -/
theorem dbarChart_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : DifferentiableAt ℂ f z₀) : dbarChart f z₀ = 0 :=
  dbarChart_eq_zero_of_hasDerivAt hf.hasDerivAt

end JacobianChallenge

end
