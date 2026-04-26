/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.PathConnected

set_option diagnostics.threshold 100

/-! # Period integral of a holomorphic 1-form along a path

This file lays the *first honest piece* of the period-integral definition for
challenge item 5 (the analytic-Jacobian construction).

## What is honestly defined here

* `pathIntegralOnInterval f c a b` — the chart-local 1-form integral
  `∫_a^b f(t)(c'(t)) dt`, where `f : ℝ → (ℂ →L[ℂ] ℂ)` is the chart-pullback of
  a covector field along the path-image and `c : ℝ → ℂ` is the chart-coordinate
  representation of the path. This is a literal `intervalIntegral` of a
  `ℂ`-valued function and carries the elementary linearity / vanishing
  properties one expects (zero, degenerate interval, reversal, constant path,
  negation, scalar multiplication, additivity, interval splitting).
* `Path.LiesInChart γ φ` — predicate: every point of the path image
  `γ(t)` lies in the source of the chart `φ : OpenPartialHomeomorph X ℂ`.
* `Path.chartCoord φ γ` — the underlying real-valued chart-coordinate map
  `t ↦ φ(γ(t))` of a `Path x x`, as a function `ℝ → ℂ` (extended by `0`
  outside the unit interval to give a global type). Honest only on `[0,1]`.

## What is NOT defined here, and why

The *intrinsic* path integral
`∫_γ ω := ∫₀¹ ω(γ(t))(γ'(t)) dt`
on a complex manifold requires either

1. a chart-by-chart construction (Lebesgue-cover the unit interval by
   intervals whose images lie inside single charts, sum the chart-local
   integrals, prove independence of cover), or
2. a Bochner-integral-on-manifolds API that mathlib does not yet ship.

Both (1) and (2) are genuine unwritten infrastructure, not five-line
adapters. **Per the project's strict-reader rule (`OPEN.md`), shipping a
`PathIntegral` whose body is `0` or an indicator-of-contained-in-chart is
strictly worse than not shipping it at all** — it would mislead a reviewer
into thinking the integral is defined when only its type is, and it would
silently agree with the trivial answer `0` for every period.

So we stop at the chart-local building block. The next file in the chain
should:

* prove the chart-local integral is independent of chart choice when two
  charts overlap on the path (Cauchy–Riemann + holomorphic transition);
* extend to non-contained paths via Lebesgue covering;
* define `Period ω : Set ℂ` as the image over all base points and all
  closed `C¹` loops at each base point;
* define `PeriodLattice X` as the integer span (`AddSubgroup.zmultiples`
  applied to the period set, viewed inside the dual of `HolomorphicOneForm`).

Those are the next milestones, not this one.

## Design notes

`pathIntegralOnInterval` is stated for *general* `f : ℝ → (ℂ →L[ℂ] ℂ)`,
not specifically for chart-pullbacks of holomorphic 1-forms. This keeps
the building block reusable: a chart pullback of `ω : HolomorphicOneForm X`
along a chart-coordinate path produces a function of this exact type, and
also any *real* (non-holomorphic) generalisation will plug in here without
a redefinition.

The `Path.chartCoord` map extends to `ℝ` by `0` outside `[0,1]`. This is
purely a type-erasure convenience so we can hand the result to
`intervalIntegral` (which takes `ℝ → E`, not `unitInterval → E`); the
extension contributes nothing because the integral is over `0..1`. We
deliberately **do not** prove differentiability of the extended map at the
endpoints — the honest integral is over the *open* interval `(0,1)` and
mathlib's `intervalIntegral` already handles boundary measure-zero issues.

The `Path.LiesInChart` predicate is given a literal definition rather than
left as a `Prop`-stub so any downstream file can `simp` through it.
-/

open scoped Manifold Topology Bundle ContDiff Interval
open MeasureTheory intervalIntegral

noncomputable section

namespace JacobianChallenge

variable {X : Type*}

/-- The chart-local 1-form integral along an interval.

For a chart-pullback `f : ℝ → (ℂ →L[ℂ] ℂ)` of a covector field and a
chart-coordinate path `c : ℝ → ℂ`, this is the literal `intervalIntegral`
of the pointwise pairing `t ↦ f(t)(c'(t))`.

Mathematically this equals `∫_a^b f(t)(c'(t)) dt`. When `f` arises as the
pullback of a holomorphic 1-form `ω` through a chart and `c` is the
chart-coordinate representation of a `C¹` path `γ : Path x x` whose image
lies in that chart, this is the chart-local contribution to the period
integral `∫_γ ω`.

`deriv c t` is the ordinary one-variable derivative of `c` at `t`. When `c`
is not differentiable at `t`, `deriv c t = 0` by mathlib convention; this
makes the definition total but means the *honest* use case requires `c` to
be `C¹` on (an open neighbourhood of) `[a,b]`. -/
def pathIntegralOnInterval (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, f t (deriv c t)

/-- The chart-local integral of the zero covector field is zero. -/
@[simp]
theorem pathIntegralOnInterval_zero (c : ℝ → ℂ) (a b : ℝ) :
    pathIntegralOnInterval (fun _ => 0) c a b = 0 := by
  unfold pathIntegralOnInterval
  simp

/-- The chart-local integral over a degenerate interval `[a,a]` is zero. -/
@[simp]
theorem pathIntegralOnInterval_self (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a : ℝ) :
    pathIntegralOnInterval f c a a = 0 := by
  unfold pathIntegralOnInterval
  exact integral_same

/-- Reversing the bounds negates the chart-local integral. -/
theorem pathIntegralOnInterval_symm (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ) :
    pathIntegralOnInterval f c b a = - pathIntegralOnInterval f c a b := by
  unfold pathIntegralOnInterval
  exact integral_symm a b

/-- Negating the covector field negates the chart-local integral. -/
@[simp]
theorem pathIntegralOnInterval_neg (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ) :
    pathIntegralOnInterval (-f) c a b = - pathIntegralOnInterval f c a b := by
  unfold pathIntegralOnInterval
  -- `(-f) t (deriv c t) = - f t (deriv c t)` pointwise.
  have hpt : (fun t => (-f) t (deriv c t)) = fun t => - f t (deriv c t) := by
    funext t
    simp [Pi.neg_apply, ContinuousLinearMap.neg_apply]
  rw [hpt]
  exact integral_neg

/-- Scaling the covector field by a complex scalar scales the chart-local
integral. The scalar `k : ℂ` acts on the integrand pointwise via the
`Module ℂ (ℂ →L[ℂ] ℂ)` structure on continuous linear maps. -/
@[simp]
theorem pathIntegralOnInterval_smul (k : ℂ) (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ)
    (a b : ℝ) :
    pathIntegralOnInterval (k • f) c a b = k • pathIntegralOnInterval f c a b := by
  unfold pathIntegralOnInterval
  -- `(k • f) t (deriv c t) = k • (f t (deriv c t))` pointwise.
  have hpt : (fun t => (k • f) t (deriv c t)) = fun t => k • f t (deriv c t) := by
    funext t
    simp [Pi.smul_apply, ContinuousLinearMap.smul_apply]
  rw [hpt]
  exact integral_smul k _

/-- Additivity of the chart-local integral in the covector field. Requires
both pointwise pairings to be `IntervalIntegrable` on `[a, b]`. -/
theorem pathIntegralOnInterval_add (f g : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ) (a b : ℝ)
    (hf : IntervalIntegrable (fun t => f t (deriv c t)) MeasureTheory.volume a b)
    (hg : IntervalIntegrable (fun t => g t (deriv c t)) MeasureTheory.volume a b) :
    pathIntegralOnInterval (f + g) c a b =
      pathIntegralOnInterval f c a b + pathIntegralOnInterval g c a b := by
  unfold pathIntegralOnInterval
  -- `(f + g) t (deriv c t) = f t (deriv c t) + g t (deriv c t)` pointwise.
  have hpt : (fun t => (f + g) t (deriv c t)) =
      fun t => f t (deriv c t) + g t (deriv c t) := by
    funext t
    simp [Pi.add_apply, ContinuousLinearMap.add_apply]
  rw [hpt]
  exact integral_add hf hg

/-- Splitting the integration interval at an intermediate point `c₀ ∈ [a, b]`.
Requires the pairing to be `IntervalIntegrable` on each subinterval. -/
theorem pathIntegralOnInterval_split (f : ℝ → ℂ →L[ℂ] ℂ) (c : ℝ → ℂ)
    (a c₀ b : ℝ)
    (hac : IntervalIntegrable (fun t => f t (deriv c t)) MeasureTheory.volume a c₀)
    (hcb : IntervalIntegrable (fun t => f t (deriv c t)) MeasureTheory.volume c₀ b) :
    pathIntegralOnInterval f c a c₀ + pathIntegralOnInterval f c c₀ b =
      pathIntegralOnInterval f c a b := by
  unfold pathIntegralOnInterval
  exact integral_add_adjacent_intervals hac hcb

/-- For a *constant* path `c ≡ p`, the chart-local integral vanishes:
the velocity `deriv c t = 0` everywhere, so the integrand is identically `0`.

This is the honest, chart-local witness that "no movement ⇒ no period
contribution". The corresponding intrinsic statement — that the period
integral of any holomorphic 1-form along a constant loop is zero — is what
this lemma is the building block for. -/
theorem pathIntegralOnInterval_const_path (f : ℝ → ℂ →L[ℂ] ℂ) (p : ℂ) (a b : ℝ) :
    pathIntegralOnInterval f (fun _ => p) a b = 0 := by
  unfold pathIntegralOnInterval
  -- `deriv (fun _ => p) t = 0` for every `t`.
  have hderiv : ∀ t : ℝ, deriv (fun _ : ℝ => p) t = 0 := by
    intro t
    exact deriv_const t p
  -- Hence the integrand `t ↦ f t (deriv (fun _ => p) t)` equals
  -- `t ↦ f t 0`, and `f t 0 = 0` by linearity of `f t`.
  have hzero : ∀ t : ℝ, f t (deriv (fun _ : ℝ => p) t) = 0 := by
    intro t
    rw [hderiv t]
    exact (f t).map_zero
  simp [hzero]

/-- Predicate: the image of a path lies in the source of a given chart.

`γ : Path x y` with `γ.LiesInChart φ` means every point `γ t : X` (for
`t : unitInterval`) lies in `φ.source`, so the chart can be applied
pointwise along the path.

This is purely topological — no smoothness, no holomorphy. The honest
use-case is: pick a chart `φ` covering a tubular neighbourhood of the
path image, then `γ.chartCoord φ` is well-defined on `[0,1]`. -/
def _root_.Path.LiesInChart {x y : X} [TopologicalSpace X] [ChartedSpace ℂ X]
    (γ : Path x y) (φ : OpenPartialHomeomorph X ℂ) : Prop :=
  ∀ t : unitInterval, γ t ∈ φ.source

/-- The chart-coordinate representation of a path that lies in a chart.

Given `γ : Path x y` with `γ.LiesInChart φ`, the map
`t ↦ φ (γ ⟨t, ht⟩)` is well-defined on `[0,1]`. We extend it to all of `ℝ`
by `0` outside `[0,1]` to make the result a global function `ℝ → ℂ` that
can be fed to `intervalIntegral` directly.

The extension is **not** continuous at the endpoints in general, but the
period integral is over `0..1` only, and `intervalIntegral` is insensitive
to endpoint values (boundary has Lebesgue measure zero). -/
def _root_.Path.chartCoord [TopologicalSpace X] [ChartedSpace ℂ X]
    {x y : X} (φ : OpenPartialHomeomorph X ℂ)
    (γ : Path x y) (_h : γ.LiesInChart φ := by intro _; trivial) : ℝ → ℂ :=
  fun t =>
    if ht : t ∈ unitInterval then
      φ (γ ⟨t, ht⟩)
    else
      0

/-- On the unit interval the chart-coordinate path agrees with the literal
chart application along `γ`. -/
theorem _root_.Path.chartCoord_apply [TopologicalSpace X] [ChartedSpace ℂ X]
    {x y : X} (φ : OpenPartialHomeomorph X ℂ) (γ : Path x y)
    (h : γ.LiesInChart φ) {t : ℝ} (ht : t ∈ unitInterval) :
    γ.chartCoord φ h t = φ (γ ⟨t, ht⟩) := by
  unfold Path.chartCoord
  simp [ht]

/-- Outside the unit interval the chart-coordinate path is `0` by
convention. This branch never contributes to the period integral. -/
theorem _root_.Path.chartCoord_of_not_mem [TopologicalSpace X]
    [ChartedSpace ℂ X] {x y : X} (φ : OpenPartialHomeomorph X ℂ)
    (γ : Path x y) (h : γ.LiesInChart φ) {t : ℝ} (ht : t ∉ unitInterval) :
    γ.chartCoord φ h t = 0 := by
  unfold Path.chartCoord
  simp [ht]

end JacobianChallenge

end
