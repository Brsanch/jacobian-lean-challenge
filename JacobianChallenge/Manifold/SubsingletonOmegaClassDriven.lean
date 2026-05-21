/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonFromBSLBAndAdmissibility
import JacobianChallenge.Manifold.HasAdmissibleChartCoverClass
import JacobianChallenge.Manifold.HasBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Typeclass-driven `Subsingleton (HolomorphicOneForm X)` from BSLB + admissibility classes

Combines:

* `[HasBasedSmoothLoopsBound X]` (in
  `Manifold/HasBasedSmoothLoopsBound.lean`) — Prop class wrapping
  `∃ p₀, BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀`.
* `[HasAdmissibleChartCover X]` (in
  `Manifold/HasAdmissibleChartCoverClass.lean`) — Prop class wrapping
  `∀ om, PathPrimitiveAdmissibleChartCover om`.

into a single theorem producing `Subsingleton (HolomorphicOneForm X)`
via `subsingleton_of_BSLB_and_universalAdmissibility`.

The basepoint is extracted from the BSLB class via `Classical.choose`.

## What ships

* `subsingleton_holomorphicOneForm_of_classes` — the headline.
* `holomorphicOneFormSubsingletonOfSimplyConnected_of_classes` —
  the SimplyConnectedSpace-conditional variant.

## Discharge witness

Both typeclasses fire unconditionally on `RiemannSphere` (via in-tree
instances), so the chain produces `Subsingleton (HolomorphicOneForm
RiemannSphere)` automatically (matching the existing direct instance
from `Manifold/RiemannSphereChartSCoeffOverlap.lean`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Subsingleton (HolomorphicOneForm X)` from
`[HasBasedSmoothLoopsBound X]` + `[HasAdmissibleChartCover X]`.**

Extracts the BSLB basepoint via `Classical.choose` of the typeclass
witness, the universal admissibility from the
`HasAdmissibleChartCover.admit` field, and feeds both into
`subsingleton_of_BSLB_and_universalAdmissibility`. -/
theorem subsingleton_holomorphicOneForm_of_classes
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [hBSLB : HasBasedSmoothLoopsBound X]
    [HasAdmissibleChartCover X] :
    Subsingleton (HolomorphicOneForm X) :=
  let ⟨p₀, h⟩ := Classical.choice ⟨hBSLB.out⟩
  subsingleton_of_BSLB_and_universalAdmissibility p₀ h
    HasAdmissibleChartCover.admit

/-- **`HolomorphicOneFormSubsingletonOfSimplyConnected X` from the same
typeclasses.** Vacuous on `SimplyConnectedSpace X` since the conclusion
is class-supplied, but exposes the same Subsingleton instance in the
SimplyConnectedSpace-conditional shape used by item 14's reverse leg
plumbing. -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_classes
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasBasedSmoothLoopsBound X] [HasAdmissibleChartCover X] :
    HolomorphicOneFormSubsingletonOfSimplyConnected X := fun _ =>
  subsingleton_holomorphicOneForm_of_classes X

end JacobianChallenge

end
