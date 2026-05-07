/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import JacobianChallenge.Analysis.L2OnManifold
import JacobianChallenge.Analysis.CompactManifoldMeasureFromCharts

/-! # `H¹` Sobolev space on a compact charted manifold (foundational chip)

This file defines a *Sobolev `H¹`* type on a compact charted manifold,
building on:

* `Analysis/L2OnManifold.lean` (ZZ128) — the abstract `IsL2` predicate
  expressed as `MemLp _ 2 _`.
* `Analysis/CompactManifoldMeasureFromCharts.lean` (ZZ143) — the
  unconditional finite measure `compactManifoldMeasureUnconditional`
  on a compact charted manifold.

Mathlib's pinned `SobolevInequality` machinery covers `Hˢ(ℝⁿ)` only;
there is no manifold-level Sobolev space in mathlib at the pin. We
therefore supply our own *predicate-based* wrapper that:

* requires the underlying `M → ℝ` to be `L²` against the unconditional
  compact-manifold measure, and
* carries a chart-side predicate `ChartDerivativeL2 f` asserting that
  the chart pullbacks have an `L²` weak derivative.

The predicate `ChartDerivativeL2` is kept *abstract* at this layer
(packaged as the sentinel `True`-equivalent predicate
`ChartDerivativeL2 := fun _ => True`) so the structure is non-empty
unconditionally. Subsequent chips will refine it to the genuine
chart-pullback Sobolev condition (via `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`
or `Mathlib.Analysis.Distribution.SchwartzSpace` plus the manifold's
`mfderiv`). At that point this predicate becomes a `def` rather than
a `True`-stub; downstream consumers depending only on the structure's
*shape* are insulated from that refinement.

## Scope

This chip provides the *type definition* plus the elementary
`Zero`/`Add` instances. It does **not**:

* prove `H¹ ↪ L²` is compact (Rellich–Kondrachov);
* prove completeness of `H¹` as a Hilbert space;
* prove the Poincaré inequality;
* tie `ChartDerivativeL2` to `mfderiv`.

Each of those is a separate downstream chip.
-/

noncomputable section

namespace JacobianChallenge

open MeasureTheory

/-- **Predicate placeholder** for "every chart pullback of `f` has an
`L²` weak first derivative on its chart codomain". This is stubbed to
the trivial predicate at this layer; a downstream chip will refine
it to the genuine condition `∀ x : M, MemLp (fderiv ℝ (f ∘ (extChartAt I x).symm)) 2 (volume.restrict (extChartAt I x).target)`.

Stubbing here lets downstream files commit against a stable name and
shape (`Prop`) without those files needing to be rewritten when the
predicate is refined. -/
def ChartDerivativeL2 {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (_f : M → ℝ) : Prop := True

/-- The chart-derivative predicate is satisfied by the zero function. -/
lemma chartDerivativeL2_zero {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ChartDerivativeL2 (n := n) (M := M) (fun _ => (0 : ℝ)) := by
  trivial

/-- The chart-derivative predicate is closed under pointwise sums.
At the stub layer this is trivial; once `ChartDerivativeL2` is
refined to the genuine `MemLp`-on-charts condition, the proof of
this lemma becomes nontrivial (it is the chart-side analogue of
`MemLp.add`). -/
lemma chartDerivativeL2_add {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {f g : M → ℝ}
    (_hf : ChartDerivativeL2 (n := n) (M := M) f)
    (_hg : ChartDerivativeL2 (n := n) (M := M) g) :
    ChartDerivativeL2 (n := n) (M := M) (fun x => f x + g x) := by
  trivial

/-- **`H¹` Sobolev space** on a compact charted manifold.

A real-valued function `M → ℝ` belongs to `H¹` iff:

* it is `L²` against the unconditional compact-manifold finite measure
  `compactManifoldMeasureUnconditional n M`, and
* every chart pullback has an `L²` weak first derivative
  (carried by the predicate `ChartDerivativeL2`).

The chart-derivative predicate is currently stubbed to `True`; see the
file-level docstring for the refinement plan. -/
structure H1OnCompactManifold (n : ℕ) (M : Type)
    [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MeasurableSpace M] where
  /-- The underlying function `M → ℝ`. -/
  toFun : M → ℝ
  /-- The function is `L²` against the unconditional compact-manifold
  measure. -/
  isL2 : IsL2 (compactManifoldMeasureUnconditional n M) toFun
  /-- Every chart pullback has an `L²` weak first derivative. -/
  hasChartDerivativeL2 : ChartDerivativeL2 (n := n) (M := M) toFun

namespace H1OnCompactManifold

variable {n : ℕ} {M : Type}
  [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M]

/-- The zero element of `H¹(M)`: the constant zero function, which is
trivially `L²` and trivially satisfies the chart-derivative predicate. -/
def zero : H1OnCompactManifold n M where
  toFun := fun _ => 0
  isL2 := isL2_zero (compactManifoldMeasureUnconditional n M)
  hasChartDerivativeL2 := chartDerivativeL2_zero

instance : Zero (H1OnCompactManifold n M) := ⟨zero⟩

@[simp] lemma zero_toFun :
    (0 : H1OnCompactManifold n M).toFun = (fun _ => (0 : ℝ)) := rfl

/-- Pointwise sum of two `H¹` functions. The `L²` part follows from
`MemLp.add`; the chart-derivative part is the (currently stubbed)
`chartDerivativeL2_add`. -/
def add (f g : H1OnCompactManifold n M) : H1OnCompactManifold n M where
  toFun := fun x => f.toFun x + g.toFun x
  isL2 := by
    have h := MemLp.add f.isL2 g.isL2
    simpa [IsL2, Pi.add_apply] using h
  hasChartDerivativeL2 :=
    chartDerivativeL2_add f.hasChartDerivativeL2 g.hasChartDerivativeL2

instance : Add (H1OnCompactManifold n M) := ⟨add⟩

@[simp] lemma add_toFun (f g : H1OnCompactManifold n M) :
    (f + g).toFun = (fun x => f.toFun x + g.toFun x) := rfl

end H1OnCompactManifold

end JacobianChallenge

end
