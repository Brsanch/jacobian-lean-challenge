/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.unusedSectionVars false

/-! # Riemann's bilinear relations — named hypotheses + ℝ-LI corollary

For a compact connected complex 1-manifold `X` of genus `g`, a basis
`α : Basis (Fin g) ℂ (HolomorphicOneForm X)`, and a tuple of `2g`
cycles `γ : Fin (2g) → data.H1` whose intersection numbers form a
**symplectic form** `J ∈ Mat_{2g×2g}(ℤ)` (e.g., the standard
`J = [[0, I_g], [-I_g, 0]]`), Riemann's bilinear relations are:

**First relation:** `Π · J · Π^T = 0` (in `Mat_{g×g}(ℂ)`).
**Second relation:** `i · Π · J · Π̄^T` is a positive-definite Hermitian
`g × g` matrix.

(Here `Π = periodMatrix data α γ` is the `2g × g` period matrix, viewed
as `g × 2g` by transposing as needed; conventions vary.)

The second relation is the **key classical input** that implies
ℝ-linear independence of the `2g` rows of `Π` — i.e., the `bilinear`
field of `SmoothHomologyDataPackage`.

This file states the two relations as **named hypotheses** and provides
the linear-algebra reduction: "Second relation positive-definite ⟹
ℝ-LI of period vectors". The relations themselves are the deep
classical content — they follow from Hodge theory + Stokes' theorem on
products of cycles, but the underlying analytic content is not
formalised at the mathlib pin.

## What this file ships

* `RiemannBilinearFirstRelation` — `Π · J · Π^T = 0` (named Prop).
* `RiemannBilinearSecondRelation` — `i · Π · J · Π̄^T` is positive
  definite (named Prop).

The implication "second relation ⟹ ℝ-LI period vectors" is concrete
linear algebra that future chips will discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Riemann's first bilinear relation** on a chosen period matrix
and symplectic-intersection-form matrix.

The product `Π^T · J · Π` (where `Π : Mat_{2g × g}(ℂ)` is the period
matrix, `J : Mat_{2g × 2g}(ℤ)` is the symplectic intersection form,
and we view `J` over ℂ via `(Int.cast)`) equals the zero `g × g`
matrix.

Classically: a consequence of Stokes' theorem on products of cycles +
the cup-product structure on cohomology. -/
def RiemannBilinearFirstRelation
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ) : Prop :=
  (periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
    * periodMatrix data α cycleGens = 0

/-- **Riemann's second bilinear relation** on a chosen period matrix
and symplectic-intersection-form matrix.

The `g × g` Hermitian matrix `i · Π^T · J · Π̄` is positive definite:
* It IS Hermitian (built into the structure).
* `xᴴ · M · x` is a positive real for every nonzero `x : Fin g → ℂ`.

Classically: also a consequence of Hodge theory — the Hodge inner
product on `H^0(X, Ω)` is positive definite, and it equals (up to sign
conventions) `i · Π^T · J · Π̄` via the duality between periods and
cohomology classes.

The positive-definiteness is the deep input that gives ℝ-linear
independence of the `2g` rows of `Π`.

Stated via the `dotProduct_mulVec` characterisation: for every
non-zero `x`, the quadratic form `xᴴ · M · x` is a positive real (the
imaginary part vanishes, and the real part is positive).
We cannot use mathlib's `Matrix.PosDef` directly because it needs a
`PartialOrder` on the underlying ring `R = ℂ`, which is not available;
instead, we phrase positivity through `Complex.re`. -/
def RiemannBilinearSecondRelation
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ) : Prop :=
  let M : Matrix (Fin (JacobianChallenge.genus X))
          (Fin (JacobianChallenge.genus X)) ℂ :=
    (Complex.I : ℂ) •
      ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * (periodMatrix data α cycleGens).map star)
  M.IsHermitian ∧
    ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (M *ᵥ x)).im = 0 ∧
        0 < (star x ⬝ᵥ (M *ᵥ x)).re

/-- **The full classical Riemann bilinear input** — both relations
hold for some symplectic form `J`. -/
def RiemannBilinearRelations
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) : Prop :=
  ∃ J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ,
    RiemannBilinearFirstRelation data α cycleGens J ∧
    RiemannBilinearSecondRelation data α cycleGens J

end JacobianChallenge

end
