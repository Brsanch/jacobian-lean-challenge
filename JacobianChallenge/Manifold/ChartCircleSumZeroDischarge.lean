/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartCircleSumZero
import JacobianChallenge.Manifold.GlobalResidueSum

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Discharge of `chartCircleSum f S r = 0` against the integer bundle

This file closes the **complex-valued** chart-circle zero-sum identity

```
chartCircleSum f S r = 0
```

(named in `ChartCircleSumZero.lean` as Z2.A) by reducing it to the
integer-coefficient identity `∑ x ∈ S, chartIntegral x = 0` already
established in `GlobalResidueSum.lean` (Z2/S1, `global_sum_zero_of_hypothesis`).

## What this commit (Z2.C) ships

Given a `GlobalResidueSum.GlobalResidueSum_hypothesis f` (which delivers
the integer chart-circle residues `chartIntegral : X → ℤ` together with
`∑ chartIntegral = 0` on `S`) **plus** a per-point bridge identifying the
complex chart-circle integral with the integer residue at the user-supplied
radius, the complex sum

```
chartCircleSum f S r = ∑ x ∈ S, chartCircleIntegralAnchored f x (r x)
```

is identically zero. The reduction is purely arithmetic:

```
chartCircleSum f S r
  = ∑ x ∈ S, (chartIntegral x : ℂ)
  = ((∑ x ∈ S, chartIntegral x : ℤ) : ℂ)
  = ((0 : ℤ) : ℂ)
  = 0.
```

The first step uses the per-point bridge `chartCircleIntegralAnchored f x (r x)
= (chartIntegral x : ℂ)`; the third uses
`GlobalResidueSum.global_sum_zero_of_hypothesis`.

## What this commit does NOT do

* It does not produce a `GlobalResidueSum_hypothesis` from raw side
  conditions; that is the integer-level Stokes leg already named in
  `GlobalResidueSum.lean`.
* It does not produce the per-point bridge from raw side conditions; that
  is the local-Cauchy / Laurent leg owned by Y1+Z1
  (`logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`).
  Note: Y1+Z1 deliver the bridge at *some* radius from the existential
  in `logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`;
  matching that radius to the user-supplied `r x` is the bundle's job at
  construction time.

## Anti-cheat

* No `axiom`, no `sorry`.
* The bundle's `chartCircleIntegral_eq_intResidue` field is **not** the
  conclusion (`= 0`); it is the per-point bridge to the integer residue.
  The conclusion `chartCircleSum = 0` is proven by combining this bridge
  with the integer sum-zero from `GlobalResidueSum`.
* No existing definition or signature is changed. This file only consumes
  the Z2.A bundle (`ChartCircleSumZero_hypothesis`) and the
  S1 bundle (`GlobalResidueSum_hypothesis`).
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Bridge bundle: complex chart-circle integral ↔ integer residue

The `GlobalResidueSum_hypothesis` carries the integer per-point residue
`chartIntegral x : ℤ`. To translate into the complex `chartCircleSum`, we
need the per-point identity

```
chartCircleIntegralAnchored f x (r x) = (H.chartIntegral x : ℂ)
```

for each `x ∈ H.S`, evaluated at the *bundle-specified* radii. This is the
Y1 / Z1 local-Cauchy output (see
`logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic` and
`logDerivResiduePlusAnalyticAnchored_holds`), but at the user-supplied
radius `r x` rather than the existential radius. -/

/-- **Bridge from `GlobalResidueSum_hypothesis` to chart-circle sum.**

This bundle augments a `GlobalResidueSum.GlobalResidueSum_hypothesis f` with
the per-point identification of the complex chart-circle integral with the
integer residue at the given radii `r x`. It is the input the
discharge `chartCircleSum_eq_zero_of_globalResidueSumBridge` consumes.

Fields:
* `toGlobal` — the integer-level bundle (`GlobalResidueSum_hypothesis f`),
  carrying `chartIntegral : X → ℤ`, `chartIntegral_eq_order`, and the two
  named gaps `chain_boundary_decomposition`, `global_chain_boundary_eq_zero`;
* `r` — the per-point chart-disk radii;
* `chartCircleIntegral_eq_intResidue` — the per-point bridge
  `chartCircleIntegralAnchored f x (r x) = ((chartIntegral x : ℤ) : ℂ)`.

Note that the bridge field is **not** `chartCircleSum f S r = 0` (that
would be the stub-green pattern of asserting the conclusion). It is a
pointwise residue identification — the kind the Y1+Z1 local leg produces. -/
structure ChartCircleSum_globalResidueBridge
    (f : MeromorphicNonzero X) where
  /-- The underlying integer-level bundle. -/
  toGlobal : JacobianChallenge.GlobalResidueSum.GlobalResidueSum_hypothesis f
  /-- The per-point chart-disk radii. -/
  r : X → ℝ
  /-- **Per-point bridge.** For each `x ∈ S`, the complex chart-circle
      integral at radius `r x` equals the integer residue cast to `ℂ`. -/
  chartCircleIntegral_eq_intResidue : ∀ x ∈ toGlobal.S,
    chartCircleIntegralAnchored f x (r x) =
      ((toGlobal.chartIntegral x : ℤ) : ℂ)

/-! ## Headline lemma: `chartCircleSum f S r = 0` -/

/-- **From the bridge to `chartCircleSum f S r = 0`.**

The complex chart-circle sum equals zero by reduction to the integer
sum-zero identity in `GlobalResidueSum.global_sum_zero_of_hypothesis`. The
proof chain is:

```
chartCircleSum f S r
  = ∑ x ∈ S, chartCircleIntegralAnchored f x (r x)        -- by definition
  = ∑ x ∈ S, ((chartIntegral x : ℤ) : ℂ)                  -- bridge field
  = (((∑ x ∈ S, chartIntegral x : ℤ) : ℤ) : ℂ)            -- Int.cast on Finset.sum
  = ((0 : ℤ) : ℂ)                                         -- global_sum_zero_of_hypothesis
  = 0.
```
-/
theorem chartCircleSum_eq_zero_of_globalResidueSumBridge
    {f : MeromorphicNonzero X}
    (B : ChartCircleSum_globalResidueBridge f) :
    chartCircleSum f B.toGlobal.S B.r = 0 := by
  -- Step 1: unfold and substitute the per-point bridge.
  unfold chartCircleSum
  have h_pt : ∀ x ∈ B.toGlobal.S,
      chartCircleIntegralAnchored f x (B.r x) =
        ((B.toGlobal.chartIntegral x : ℤ) : ℂ) :=
    B.chartCircleIntegral_eq_intResidue
  rw [Finset.sum_congr rfl h_pt]
  -- Step 2: integer sum-zero from `GlobalResidueSum`.
  have h_int_sum_zero :
      ∑ x ∈ B.toGlobal.S, B.toGlobal.chartIntegral x = 0 :=
    JacobianChallenge.GlobalResidueSum.global_sum_zero_of_hypothesis B.toGlobal
  -- Step 3: pull the cast through the sum and conclude.
  -- `∑ x, ((n x : ℤ) : ℂ) = ((∑ x, n x : ℤ) : ℂ) = ((0 : ℤ) : ℂ) = 0`.
  have h_cast :
      (∑ x ∈ B.toGlobal.S, ((B.toGlobal.chartIntegral x : ℤ) : ℂ))
        = (((∑ x ∈ B.toGlobal.S, B.toGlobal.chartIntegral x : ℤ) : ℤ) : ℂ) := by
    push_cast
    rfl
  rw [h_cast, h_int_sum_zero, Int.cast_zero]

/-! ## Discharge of the `ChartCircleSumZero_hypothesis` side conditions

Given a Z2.A `ChartCircleSumZero_hypothesis` matching the bridge's shape,
the same conclusion holds: `chartCircleSum f S r = 0`. The Z2.A bundle's
side conditions (chart-target witness, disjoint disks, support inclusion)
are independent of and compatible with the bridge's per-point integer
identification — they constrain the *geometry* of the chart-circles, while
the bridge constrains the *value* of each chart-circle integral. -/

/-- **Compatibility predicate.** A `ChartCircleSumZero_hypothesis f S r`
and a `ChartCircleSum_globalResidueBridge f` are *aligned* when they refer
to the same finite set `S` and the same per-point radii `r`. This is
recorded as a `Prop`-valued definition rather than baked into the bundle,
so callers can mix-and-match different geometric and arithmetic inputs. -/
def ChartCircleSumZero_hypothesis_aligned
    {f : MeromorphicNonzero X} {S : Finset X} {r : X → ℝ}
    (_H : ChartCircleSumZero_hypothesis f S r)
    (B : ChartCircleSum_globalResidueBridge f) : Prop :=
  S = B.toGlobal.S ∧ (∀ x ∈ S, r x = B.r x)

/-- **From an aligned Z2.A bundle plus the bridge: `chartCircleSum f S r = 0`.**

The Z2.A bundle's geometric side conditions are not required for this
arithmetic conclusion (they will be required by any *honest* construction
of a `ChartCircleSum_globalResidueBridge`, since the bridge's per-point
identity ultimately depends on the chart-circle being inside the chart
target and the disks being pairwise disjoint to apply local Cauchy). They
are inputs to the *construction* of the bridge, not to its consumption. -/
theorem chartCircleSum_eq_zero_of_aligned
    {f : MeromorphicNonzero X} {S : Finset X} {r : X → ℝ}
    (H : ChartCircleSumZero_hypothesis f S r)
    (B : ChartCircleSum_globalResidueBridge f)
    (h_align : ChartCircleSumZero_hypothesis_aligned H B) :
    chartCircleSum f S r = 0 := by
  obtain ⟨hS, hr⟩ := h_align
  -- Rewrite `S` to `B.toGlobal.S` and `r` to `B.r` on `S`.
  rw [hS] at hr ⊢
  rw [chartCircleSum_congr f B.toGlobal.S hr]
  exact chartCircleSum_eq_zero_of_globalResidueSumBridge B

end MeromorphicNonzero

end JacobianChallenge

end
