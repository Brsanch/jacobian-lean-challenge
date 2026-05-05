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

end MeromorphicNonzero

end JacobianChallenge

end
