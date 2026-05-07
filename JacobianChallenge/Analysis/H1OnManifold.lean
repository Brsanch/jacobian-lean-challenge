/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib
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
  for every chart `φ` in the atlas, the chart pullback
  `f ∘ φ.symm : EuclideanSpace ℝ (Fin n) → ℝ` is differentiable on
  the chart target and its Fréchet derivative is in `L²` of the
  Lebesgue measure restricted to that target.

This file *replaces* an earlier `True`-stub form of `ChartDerivativeL2`
(ZZ146) with the genuine chart-pullback `MemLp` content (ZZ148).
The shape (a `Prop` named `ChartDerivativeL2` plus the `Zero`/`Add`
instances on `H1OnCompactManifold`) is preserved so downstream files
binding only against the predicate's name keep building.

## Implementation note: the predicate carries `MemLp` of the derivative

We require `MemLp (fun x => fderiv ℝ (f ∘ φ.symm) x) 2 (volume.restrict φ.target)`,
i.e. `L²`-membership of the *continuous-linear-map-valued* Fréchet
derivative itself, not merely its norm. This is the form mathlib
uses for `Lᵖ`-spaces of vector-valued functions, and crucially it
gives us AE strong measurability of `fderiv ℝ (f ∘ φ.symm)` (rather
than only of its norm), which is what makes the additivity proof for
the chart-derivative predicate go through: `fderiv ℝ` of a sum on a
domain where both summands are differentiable equals the sum of the
two summand derivatives, and AE strong measurability is preserved
by addition.

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

/-- Chart-pullback Sobolev predicate.

`ChartDerivativeL2 f` says: for every chart `φ` of the atlas of the
charted-space structure on `M`,

* the chart pullback `f ∘ φ.symm : EuclideanSpace ℝ (Fin n) → ℝ` is
  differentiable on `φ.target`, and
* the Fréchet derivative `x ↦ fderiv ℝ (f ∘ φ.symm) x` (a continuous
  linear map valued function) is in `L²` of the Lebesgue volume
  restricted to `φ.target`.

Bundling differentiability into the predicate makes the chart-side
Fréchet derivative additive on overlaps of differentiability
domains. Bundling `MemLp` of the *map-valued* derivative (not just
its norm) gives AE strong measurability of the derivative, which
lets the additivity proof for `ChartDerivativeL2` go through. -/
def ChartDerivativeL2 {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → ℝ) : Prop :=
  ∀ φ ∈ atlas (EuclideanSpace ℝ (Fin n)) M,
    DifferentiableOn ℝ (f ∘ φ.symm) φ.target ∧
    MemLp (fun x => fderiv ℝ (f ∘ φ.symm) x)
      2 (volume.restrict φ.target)

/-- The chart-derivative predicate is satisfied by the zero function:
its chart pullback is the zero function, which is differentiable
everywhere with zero Fréchet derivative, and the zero function is
trivially `L²`. -/
lemma chartDerivativeL2_zero {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ChartDerivativeL2 (n := n) (M := M) (fun _ => (0 : ℝ)) := by
  intro φ _hφ
  -- The chart pullback of the zero function is the zero function on
  -- `EuclideanSpace ℝ (Fin n)`.
  have hcomp : ((fun _ : M => (0 : ℝ)) ∘ φ.symm)
        = (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) := by
    funext y; rfl
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact (differentiable_const (0 : ℝ)).differentiableOn
  · -- `fderiv` of the zero function is the zero linear map; the
    -- zero function is in `Lᵖ` for every measure.
    have hderiv :
        (fun x : EuclideanSpace ℝ (Fin n) =>
            fderiv ℝ ((fun _ : M => (0 : ℝ)) ∘ φ.symm) x)
          = (fun _ => (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) := by
      funext x
      rw [hcomp]
      simp [fderiv_const]
    rw [hderiv]
    exact MemLp.zero'

/-- The chart-derivative predicate is closed under pointwise sums.
Both summands being differentiable on each chart target lets `fderiv`
distribute, after which `MemLp.add` of the two summand derivatives,
combined with AE-equality of the sum-derivative with the sum of
derivatives on the chart target, closes the `MemLp` goal. -/
lemma chartDerivativeL2_add {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {f g : M → ℝ}
    (hf : ChartDerivativeL2 (n := n) (M := M) f)
    (hg : ChartDerivativeL2 (n := n) (M := M) g) :
    ChartDerivativeL2 (n := n) (M := M) (fun x => f x + g x) := by
  intro φ hφ
  obtain ⟨hf_diff, hf_L2⟩ := hf φ hφ
  obtain ⟨hg_diff, hg_L2⟩ := hg φ hφ
  have hcomp_eq :
      (fun x => f x + g x) ∘ φ.symm
        = (fun y => (f ∘ φ.symm) y + (g ∘ φ.symm) y) := by
    funext y; rfl
  refine ⟨?_, ?_⟩
  · rw [hcomp_eq]
    exact hf_diff.add hg_diff
  · -- The sum's derivative agrees a.e. on `φ.target` with the
    -- sum of summand derivatives, which is in `L²` by `MemLp.add`.
    have hsum_L2 :
        MemLp (fun x => fderiv ℝ (f ∘ φ.symm) x
                          + fderiv ℝ (g ∘ φ.symm) x)
          2 (volume.restrict φ.target) :=
      MemLp.add hf_L2 hg_L2
    have h_eq_ae :
        (fun x => fderiv ℝ ((fun x => f x + g x) ∘ φ.symm) x)
          =ᵐ[volume.restrict φ.target]
        (fun x => fderiv ℝ (f ∘ φ.symm) x
                  + fderiv ℝ (g ∘ φ.symm) x) := by
      refine (ae_restrict_iff' (s := φ.target) ?_).mpr ?_
      · exact φ.open_target.measurableSet
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      have hfx : DifferentiableAt ℝ (f ∘ φ.symm) x :=
        (hf_diff x hx).differentiableAt (φ.open_target.mem_nhds hx)
      have hgx : DifferentiableAt ℝ (g ∘ φ.symm) x :=
        (hg_diff x hx).differentiableAt (φ.open_target.mem_nhds hx)
      rw [hcomp_eq]
      exact fderiv_add hfx hgx
    -- `MemLp` is preserved under a.e. equality: rebuild from
    -- `aestronglyMeasurable` and `eLpNorm` finiteness, transferred
    -- across `h_eq_ae`.
    refine ⟨?_, ?_⟩
    · exact hsum_L2.aestronglyMeasurable.congr h_eq_ae.symm
    · have h_eLp : eLpNorm
            (fun x => fderiv ℝ ((fun x => f x + g x) ∘ φ.symm) x) 2
            (volume.restrict φ.target)
          = eLpNorm
            (fun x => fderiv ℝ (f ∘ φ.symm) x
                      + fderiv ℝ (g ∘ φ.symm) x) 2
            (volume.restrict φ.target) :=
        eLpNorm_congr_ae h_eq_ae
      rw [h_eLp]; exact hsum_L2.eLpNorm_lt_top

/-- **`H¹` Sobolev space** on a compact charted manifold.

A real-valued function `M → ℝ` belongs to `H¹` iff:

* it is `L²` against the unconditional compact-manifold finite measure
  `compactManifoldMeasureUnconditional n M`, and
* every chart pullback is differentiable on its chart target with
  `L²` Fréchet derivative there (carried by `ChartDerivativeL2`). -/
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
`MemLp.add`; the chart-derivative part is `chartDerivativeL2_add`. -/
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
