/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14ClassDrivenAdmissibility
import JacobianChallenge.Manifold.HasConvexTargetChartCover

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Composite item 14: chart-cover + Subsingleton-ω typeclasses + 2 inputs

Composes:

* `HasConvexTargetChartCover X` (structural — every point in a chart with convex target);
* `[Subsingleton (HolomorphicOneForm X)]` (analytic — Hodge content);
* the `instHasAdmissibleChartCoverOfConvexCoverAndSubsingletonOmega` instance;
* the class-driven 2-input item 14 chip.

Result: under the two structural typeclasses, item 14 reduces to the
**two classical inputs** `hSP` + `h_bslb`. This is the most factored
form of item 14 currently in tree.

## What this file ships

* `genus_eq_zero_iff_homeo_under_convexCover_and_subsingletonOmega` —
  the composite chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional under `[HasConvexTargetChartCover X]` +
`[Subsingleton (HolomorphicOneForm X)]`, from `hSP` + `h_bslb`.**

Composes the chart-cover typeclass with the Subsingleton-ω instance to
automatically discharge `HasAdmissibleChartCover X`, then the
class-driven 2-input item 14. -/
theorem genus_eq_zero_iff_homeo_under_convexCover_and_subsingletonOmega
    [HasConvexTargetChartCover X]
    [Subsingleton (HolomorphicOneForm X)]
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  -- HasAdmissibleChartCover follows from the two typeclasses.
  genus_eq_zero_iff_homeo_from_hSP_and_h_bslb_HasAdmissibleChartCover
    x₀ b hSP h_bslb

/-! ## RS end-to-end via the composite chip

On `RiemannSphere`, both structural typeclasses are unconditional in
tree:
* `HasConvexTargetChartCover RiemannSphere` (this session).
* `Subsingleton (HolomorphicOneForm RiemannSphere)`
  (`Manifold/RiemannSphereChartSCoeffOverlap.lean`).

So the composite chip fires from the two classical inputs alone. -/

/-- **RS end-to-end via the composite chip.** -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_composite
    (x₀ : RiemannSphere) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm RiemannSphere)) :
    JacobianChallenge.genus RiemannSphere = 0 ↔
      Nonempty (RiemannSphere ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_under_convexCover_and_subsingletonOmega x₀ b
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    (fun _ => RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds x₀)

end JacobianChallenge

end
