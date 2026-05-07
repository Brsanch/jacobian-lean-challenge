/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # `L²` sections of a normed bundle on a measure space (foundational chip)

This file is the first foundational analytic piece of the Hodge cluster.
The end goal is a usable type of `L²` sections of a Hermitian vector
bundle `V → M` over a compact charted space `M`. Building that fully
requires (a) a canonical volume measure on `M` (Riemannian or partition-
of-unity averaged) and (b) measurable bundle structure machinery that is
presently absent at the pinned mathlib commit.

To stay within scope (one foundational chip, no `sorry`, no `axiom`) we
package the *measure-theoretic core* of the construction here:

* `L2NormSq μ s` — the `ℝ≥0∞`-valued squared `L²` integral of a function
  `s : M → F` (with `F` a normed space) against a measure `μ`.
* `IsL2 μ s` — predicate: `s` is in `L²(μ; F)`, i.e. `MemLp s 2 μ`.
* `L2NormSq_zero` — easy lemma, the squared norm of the zero section is
  zero on any measure space.
* `isL2_zero` — the zero function is `L²` against any measure.

Subsequent chips will (i) define the canonical Riemannian volume measure
on a compact smooth manifold, (ii) define an `L²` predicate on sections
of a vector bundle by local pullback in charts plus a partition of
unity, and (iii) endow the resulting space with its Hilbert structure.
This chip provides the measure-theoretic substrate those later chips
will compose against.

## Implementation notes

Working over `ℝ≥0∞` rather than `ℝ` lets the squared-norm integral be
totally defined for every `s` regardless of integrability; the `IsL2`
predicate then simply asserts finiteness via mathlib's `MemLp _ 2 _`.

We deliberately keep the underlying space abstract (`α`, a measurable
space) so that this layer composes both with `α = M` (a manifold) and
with `α = ℝⁿ` (a chart codomain).
-/

noncomputable section

namespace JacobianChallenge

open MeasureTheory ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]
variable {F : Type*} [NormedAddCommGroup F]

/-- The squared `L²` norm of a function `s : α → F` against a measure
`μ`, taking values in `ℝ≥0∞`. This is `∫⁻ x, ‖s x‖₊^2 ∂μ` and is
totally defined regardless of whether `s` is in `L²`. -/
def L2NormSq (μ : Measure α) (s : α → F) : ℝ≥0∞ :=
  ∫⁻ x, (‖s x‖₊ : ℝ≥0∞) ^ 2 ∂μ

/-- A function `s : α → F` is in `L²(μ; F)` iff it satisfies mathlib's
`MemLp _ 2 _`. This is the bridge predicate that downstream
manifold-level definitions will pull back through charts. -/
def IsL2 (μ : Measure α) (s : α → F) : Prop :=
  MemLp s 2 μ

/-- The squared `L²` norm of the zero function is zero against any
measure. This is the easy lemma promised in the chip scope. -/
@[simp]
lemma L2NormSq_zero (μ : Measure α) :
    L2NormSq (F := F) μ (fun _ => (0 : F)) = 0 := by
  unfold L2NormSq
  simp

/-- The zero function is in `L²` against any measure. -/
lemma isL2_zero (μ : Measure α) :
    IsL2 (F := F) μ (fun _ => (0 : F)) := by
  unfold IsL2
  exact MeasureTheory.MemLp.zero'

/-- The squared `L²` norm is monotone in the integrand's pointwise
norm. This will be useful when bounding bundle sections by chart-
local representatives in subsequent chips. -/
lemma L2NormSq_mono {μ : Measure α} {s t : α → F}
    (h : ∀ x, ‖s x‖ ≤ ‖t x‖) :
    L2NormSq μ s ≤ L2NormSq μ t := by
  unfold L2NormSq
  refine lintegral_mono (fun x => ?_)
  have hx : (‖s x‖₊ : ℝ≥0∞) ≤ (‖t x‖₊ : ℝ≥0∞) := by
    have : ‖s x‖₊ ≤ ‖t x‖₊ := by
      rw [← NNReal.coe_le_coe]; simpa using h x
    exact_mod_cast this
  exact pow_le_pow_left' hx 2

end JacobianChallenge

end
