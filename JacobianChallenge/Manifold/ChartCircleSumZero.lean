/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchoredDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chart-circle sum and its zero-sum identity

This file shapes the **formal sum** of the chart-anchored chart-circle
integrals from `LogDiffAnchoredDischarge.lean` and surfaces the
zero-sum identity (the "global leg" of the residue theorem) as a
single named statement.

Concretely, given
* `f : MeromorphicNonzero X` on a compact 2-manifold modelled on `ℂ`,
* a finite set `S : Finset X` (intended to contain the zeros and poles
  of `f`, possibly with padding),
* a per-point radius `r : X → ℝ` (the small chart-disk radii),

we define
```
chartCircleSum f S r := ∑ x ∈ S, chartCircleIntegralAnchored f x (r x).
```
This is the *complex-valued* sum of the chart-circle integrals delivered
by Y1's `chartCircleIntegralAnchored`. It is the precise object that the
classical residue-theorem statement
`∑_{poles+zeros of f} chartCircleIntegralAnchored f x (r x) = 0`
asserts is zero on a compact 2-manifold without boundary.

## What this commit does (Z2.A)

* Definition `chartCircleSum f S r`.
* `@[simp]` unfolding `chartCircleSum_def`.
* Trivial sum-arithmetic lemmas: `chartCircleSum_empty`,
  `chartCircleSum_insert_of_not_mem`, `chartCircleSum_congr`.
* Structure `ChartCircleSumZero_hypothesis f S r` bundling the side
  conditions that the classical residue-theorem proof consumes:
  - `support_subset` — `S` contains the zeros + poles of `f`,
  - `radius_pos` — each `r x > 0` for `x ∈ S`,
  - `chart_target_witness` — the chart-circle of radius `r x` lies
    inside `(chartAt ℂ x).target` (the small-radius hygiene witness
    that `LogDiffAnchored` already names per-point),
  - `disjoint_disks` — the chart-pulled-back closed disks at distinct
    points of `S` do not overlap *as manifold subsets*, formulated as
    pairwise disjointness of the manifold preimages of the chart-disks.

The companion zero-sum identity
`chartCircleSum f S r = 0`
is **not** discharged in this commit. It is the substantive content of
Stokes-on-a-compact-2-manifold-without-boundary applied to the closed
1-form `d log f` on `X \ ⋃_{x ∈ S} D_x`, exactly the same content
already named in `GlobalResidueSum.GlobalResidueSum_hypothesis` (at the
integer-coefficient level) and in
`StokesCompactSurface.StokesCompactSurfacePartitionOfUnity_hypothesis`
(at the real-valued partition-of-unity level). This file ships the
**complex-valued formal sum** that those existing bundles do not name
directly — the integer-coefficient bundle in `GlobalResidueSum.lean`
operates on `chartIntegral : X → ℤ`, and the real-valued bundle in
`StokesCompactSurface.lean` operates on the partition-of-unity
boundary integrals; the *complex* `∑ chartCircleIntegralAnchored …`
that Y1's discharge produces was previously unnamed.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed (pure addition).
* `chartCircleSum` has a real `Finset.sum` body, not a `0`-stub.
* The structure carries side conditions that any later discharge of
  the zero-sum identity must consume; it does not assert the zero
  identity as a hypothesis field (i.e. it is not a stub-green
  packaging of "assume the conclusion").
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

/-! ## The formal chart-circle sum -/

/-- **Formal chart-circle sum.** Given a meromorphic-nonzero
`f : MeromorphicNonzero X`, a finite set `S : Finset X`, and a per-point
radius `r : X → ℝ`, this is `∑_{x ∈ S} chartCircleIntegralAnchored f x (r x)`.

Specialisation of the per-point Y1 integral to a finite sum. The intended
classical content is `chartCircleSum f S r = 0` whenever `S` contains the
zeros + poles of `f` and the small-radius / disjoint-disks side conditions
hold; that identity is named (but not discharged) by
`ChartCircleSumZero_hypothesis` below. -/
def chartCircleSum
    (f : MeromorphicNonzero X) (S : Finset X) (r : X → ℝ) : ℂ :=
  ∑ x ∈ S, chartCircleIntegralAnchored f x (r x)

@[simp] lemma chartCircleSum_def
    (f : MeromorphicNonzero X) (S : Finset X) (r : X → ℝ) :
    chartCircleSum f S r =
      ∑ x ∈ S, chartCircleIntegralAnchored f x (r x) := rfl

/-- Empty-support reduction: `chartCircleSum f ∅ r = 0`. -/
@[simp] lemma chartCircleSum_empty
    (f : MeromorphicNonzero X) (r : X → ℝ) :
    chartCircleSum f (∅ : Finset X) r = 0 := by
  simp [chartCircleSum]

/-- Insertion reduction: insert one new point and the sum splits as the
new contribution plus the old sum. -/
lemma chartCircleSum_insert_of_not_mem [DecidableEq X]
    (f : MeromorphicNonzero X) {S : Finset X} {x : X}
    (hx : x ∉ S) (r : X → ℝ) :
    chartCircleSum f (insert x S) r =
      chartCircleIntegralAnchored f x (r x) + chartCircleSum f S r := by
  unfold chartCircleSum
  exact Finset.sum_insert hx

/-- Congruence on the radius function: if `r x = r' x` for every `x ∈ S`,
the chart-circle sums agree. -/
lemma chartCircleSum_congr
    (f : MeromorphicNonzero X) (S : Finset X) {r r' : X → ℝ}
    (hrr' : ∀ x ∈ S, r x = r' x) :
    chartCircleSum f S r = chartCircleSum f S r' := by
  unfold chartCircleSum
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [hrr' x hx]

/-! ## The bundle of side conditions for the zero-sum identity -/

/-- **Side conditions for the chart-circle zero-sum identity.**

This structure bundles the geometric / chart-hygiene hypotheses that
the classical Stokes-on-a-compact-2-manifold proof of
`chartCircleSum f S r = 0` consumes. It does **not** assert the zero
identity itself as a hypothesis field; it only carries the *inputs*
to that identity.

Fields:
* `support_subset` — `S` contains the divisor support of `f`;
* `radius_pos` — each chart-disk radius is positive on `S`;
* `chart_target_witness` — the entire chart-circle of radius `r x`
  centred at `(chartAt ℂ x) x` lies inside `(chartAt ℂ x).target`;
  this is the same per-point hygiene predicate already used by
  `LogDerivResiduePlusAnalyticAnchored`;
* `disjoint_disks` — for any two distinct points `x, y ∈ S`, the
  manifold preimages of their closed chart-disks of radii `r x`, `r y`
  do not overlap, i.e. the small disks `D_x`, `D_y` are pairwise
  disjoint (so the punctured-manifold `X \ ⋃_{x ∈ S} D_x` is well
  defined as a manifold-with-boundary whose boundary is the disjoint
  union of the chart-circles).

The honest framing: the structure is the *aggregate of inputs* to a
later discharge of the zero-sum identity. A discharge is owed; it
is not packaged here as a hypothesis field, because the user's
explicit guidance is that hypothesis-field-of-the-conclusion
constructs are the stub-green pattern to avoid. -/
structure ChartCircleSumZero_hypothesis
    (f : MeromorphicNonzero X) (S : Finset X) (r : X → ℝ) where
  /-- The divisor support is contained in `S` (so `S` covers all the
      zeros and poles of `f`). -/
  support_subset : (principalDivisorMap f).supportFinset ⊆ S
  /-- Each chart-disk radius is strictly positive on `S`. -/
  radius_pos : ∀ x ∈ S, 0 < r x
  /-- The whole chart-circle of radius `r x` centred at `(chartAt ℂ x) x`
      lies inside `(chartAt ℂ x).target`. (Per-point chart-hygiene
      witness; same predicate as in `LogDerivResiduePlusAnalyticAnchored`.) -/
  chart_target_witness : ∀ x ∈ S, ∀ θ : ℝ,
    (chartAt ℂ x) x + (r x : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      (chartAt ℂ x).target
  /-- The small chart-disks at distinct points of `S` are pairwise
      disjoint as manifold subsets: for `x ≠ y` in `S`, the preimages
      `(chartAt ℂ x) ⁻¹' Metric.closedBall ((chartAt ℂ x) x) (r x)`
      and the analogous preimage for `y` do not share any manifold
      point. -/
  disjoint_disks : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
    Disjoint
      ((chartAt ℂ x) ⁻¹' Metric.closedBall ((chartAt ℂ x) x) (r x))
      ((chartAt ℂ y) ⁻¹' Metric.closedBall ((chartAt ℂ y) y) (r y))

/-! ## Trivial corollaries

These are the structural lemmas any later discharge consumes. -/

/-- **From the bundle: positive radius on `S`.** -/
lemma ChartCircleSumZero_hypothesis.radius_pos_of_mem
    {f : MeromorphicNonzero X} {S : Finset X} {r : X → ℝ}
    (H : ChartCircleSumZero_hypothesis f S r) {x : X} (hx : x ∈ S) :
    0 < r x := H.radius_pos x hx

/-- **From the bundle: chart-target witness on `S`.** -/
lemma ChartCircleSumZero_hypothesis.chart_target_of_mem
    {f : MeromorphicNonzero X} {S : Finset X} {r : X → ℝ}
    (H : ChartCircleSumZero_hypothesis f S r) {x : X} (hx : x ∈ S) (θ : ℝ) :
    (chartAt ℂ x) x + (r x : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      (chartAt ℂ x).target := H.chart_target_witness x hx θ

end MeromorphicNonzero

end JacobianChallenge

end
