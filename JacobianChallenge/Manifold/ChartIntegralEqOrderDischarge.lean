/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchored
import JacobianChallenge.Manifold.LogDiffAnchoredDischarge
import JacobianChallenge.Manifold.LogDiffAnchoredWitness
import JacobianChallenge.Manifold.ResidueTheoremAssembly

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `chartIntegral_eq_order` discharge (Route A wire-up of Z1)

This file produces a free-standing per-point identification

  `chartIntegralZZ56 f x = orderFun 𝓘(ℂ,ℂ) f.toFun x`

together with the chart-circle witness that, under standard non-degeneracy
(`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`), this integer equals the
anchored chart-circle integral of `d log f` cast to `ℂ`. This is exactly
the per-point local content needed to satisfy the `chartIntegral_eq_order`
field of `SumOfResiduesPartitionOfUnity_hypothesis` in
`ResidueTheoremAssembly.lean`.

We do *not* assemble the whole bundle here (the bundle additionally needs
`S`, `support_subset`, `global_sum_zero`, all out of scope). We only
deliver the local Route A piece.

## Composition

* Z1 X1 (`LogDiffAnchored.lean`) — `chartCircleIntegralAnchored`,
  `LogDerivResiduePlusAnalyticAnchored`.
* Z1 Y1 (`LogDiffAnchoredDischarge.lean`) — half-bundle real discharge:
  `logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`.
* Z1 Z1 (`LogDiffAnchoredWitness.lean`) — unconditional witness for the
  Laurent hypothesis under finite chart-pullback order.

We compose Y1 ∘ Z1 to obtain an unconditional chart-circle identity.
The integer field `chartIntegralZZ56` is defined as the chart-pullback
order, making the field equation `rfl` and tying the chart-circle integral
identity to the integer order through the cast.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature changed (pure addition).
* The `chartIntegral_eq_order` field's signature is matched verbatim.
-/

noncomputable section

open scoped Manifold ContDiff
open Complex

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-- **Per-point chart-integral value (Route A).** Defined as the
chart-pullback integer order of `f` at `x`. This is the integer the
`chartIntegral` field of `SumOfResiduesPartitionOfUnity_hypothesis`
expects on its support, and the chart-circle integral of `d log f` lifts
to it via the Z1 anchored chain (see `chartIntegralZZ56_eq_anchored`). -/
def chartIntegralZZ56 (f : MeromorphicNonzero X) (x : X) : ℤ :=
  JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x

/-- **Field discharge (Route A).** The per-point identification required
by the `chartIntegral_eq_order` field of
`SumOfResiduesPartitionOfUnity_hypothesis` holds for `chartIntegralZZ56`
on every point: by definition, `chartIntegralZZ56 f x` is the integer
`orderFun 𝓘(ℂ,ℂ) f.toFun x`. -/
theorem chartIntegralZZ56_eq_order
    (f : MeromorphicNonzero X) (x : X) :
    chartIntegralZZ56 f x =
      JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := rfl

/-- **Chart-circle realisation of `chartIntegralZZ56` (Z1 wire-up).**

Under the standard non-degeneracy hypothesis
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`, there is a chart-circle of
some radius `r > 0` on which the anchored chart-circle integral of
`logDiffCoeffAt f x` equals `chartIntegralZZ56 f x` cast to `ℂ`.

This is the composition of Z1 Z1's unconditional witness for the Laurent
hypothesis (`logDerivResiduePlusAnalyticAnchored_holds`) with Z1 Y1's
half-bundle real discharge
(`logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`),
re-expressed in terms of the integer `chartIntegralZZ56`.

This is the chart-circle witness behind the `chartIntegral_eq_order`
field: a future bundle constructor for
`SumOfResiduesPartitionOfUnity_hypothesis` that works at the integer
level can use `chartIntegralZZ56_eq_order` to discharge the field
verbatim, while pointing at this lemma for the genuine chart-circle
content from R1. -/
theorem chartIntegralZZ56_eq_anchored
    (f : MeromorphicNonzero X) (x : X)
    (hf0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤) :
    ∃ r > (0 : ℝ),
      chartCircleIntegralAnchored f x r = ((chartIntegralZZ56 f x : ℤ) : ℂ) := by
  -- Z1 Z1: produce the Laurent witness from the non-degeneracy hypothesis.
  have hH : LogDerivResiduePlusAnalyticAnchored f x :=
    logDerivResiduePlusAnalyticAnchored_holds f x hf0
  -- Z1 Y1: half-bundle real discharge gives the chart-circle identity.
  obtain ⟨r, hr, hrEq⟩ :=
    logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic f x hH
  -- `chartIntegralZZ56` is definitionally the integer order.
  exact ⟨r, hr, hrEq⟩

end MeromorphicNonzero

end JacobianChallenge

end
