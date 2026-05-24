/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromLoopPeriodVanishesUnconditional
import JacobianChallenge.Manifold.LoopPeriodVanishesOfBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # `S2ImpliesGenus0 X` from single-basepoint BSLB UNCONDITIONALLY

Strictly stronger arbitrary-X reduction than
`S2ImpliesGenus0FromBasedSmoothLoopsBound.lean` (which requires
per-basis `h_smooth_b` and `h_ftc_b` inputs alongside BSLB). The
chartLocalPrimitive maxAtlas cascade (steps 1–7 this session)
discharges those analytic inputs unconditionally; this file ships
the reduction theorem that uses only:

* BSLB at a single basepoint x₀ (under SimplyConnectedSpace X);
* the in-tree `simplyConnectedS2_holds` and
  `smoothPathConnected_of_preconnected`.

## Place in the architecture

Per `SubdivisionTelescopingToLoopFromBSLB.lean`, universal BSLB ⟹
`SubdivisionTelescopingToLoop_named X`. The
`chartContainedLoopVanishingHypothesis_holds_unconditional` (in tree,
unconditional via `PointwiseChartEvalUnconditional.lean`) makes
`LoopPeriodVanishes` depend only on `SubdivisionTelescopingToLoop_named`.
And this session's cascade discharges the primitive-existence content
of `HolomorphicOneFormSubsingletonOfSimplyConnected` once
`LoopPeriodVanishes` is available.

The chip above (`S2ImpliesGenus0FromSubdivisionTelescopingUnconditional.lean`)
went through `SubdivisionTelescopingToLoop_named`. This file shortcuts
through single-basepoint BSLB instead, which is the smaller and more
classical hypothesis (the empty subdivision-list witness gives
`SubdivisionTelescopingToLoop_named` from BSLB, then the chain runs;
here we route directly without explicit subdivision).

## What's open after this commit

* `SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` —
  the genuine remaining classical content. Discharged unconditionally
  on `RiemannSphere` (via `basedSmoothLoopsBoundHypothesis_RS_holds`,
  missed-point + Möbius shift) and on `ℂ` (straight-line contraction),
  both in tree. Arbitrary-X discharge is the smooth Hurewicz step.

## What this file ships

* `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis_unconditional` —
  closes `S2ImpliesGenus0 X` from a single hypothesis
  `SimplyConnectedSpace X → BSLB 𝓘(ℝ, ℂ) X x₀` at a chosen basepoint.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from single-basepoint BSLB.**

Composes
* `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis` (in tree)
  to derive `∀ om, LoopPeriodVanishes om x₀` from BSLB at x₀;
* `s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected` (this
  session, step 7) to close S2ImpliesGenus0 X using the cascade's
  unconditional smoothness + FTC.

Strictly stronger than `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis`
in `S2ImpliesGenus0FromBasedSmoothLoopsBound.lean`: that earlier
chain still consumes per-basis smoothness + FTC as inputs; here both
are discharged by the cascade (steps 1–6 of HANDOFF_ITEM14.md). -/
theorem s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis_unconditional
    (x₀ : X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected x₀ <| fun h_sc om =>
    loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis (h_bslb h_sc) om

end JacobianChallenge

end
