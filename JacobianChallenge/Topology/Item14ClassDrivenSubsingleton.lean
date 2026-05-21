/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonOmegaClassDriven
import JacobianChallenge.Topology.HTopFromSubsingleton

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 from `[HasBSLB] + [HasAdmissibleChartCover] + hSP` via Subsingleton

A **typeclass-driven** route to item 14 closure: the only non-class
input is the forward-leg simple-pole-germ existence `hSP`.

The reverse leg is fully discharged from the typeclass instances:

* `[HasBasedSmoothLoopsBound X]` + `[HasAdmissibleChartCover X]`
  → `Subsingleton (HolomorphicOneForm X)`
  (via `subsingleton_holomorphicOneForm_of_classes`);
* `[Subsingleton (HolomorphicOneForm X)]` + `hSP`
  → item 14 biconditional
  (via `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`).

This is the cleanest item-14 closure shape for downstream consumers
that supply the analytic content via typeclass instances rather than
as Prop hypotheses.

For `X = RiemannSphere`, the typeclass instances are in tree, so the
chain is **fully unconditional** modulo `hSP` (which is itself
unconditional on RS).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 from `[HasBasedSmoothLoopsBound X] + [HasAdmissibleChartCover X]
+ hSP`.** -/
theorem genus_eq_zero_iff_homeo_class_driven_via_subsingleton
    [HasBasedSmoothLoopsBound X] [HasAdmissibleChartCover X]
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  haveI : Subsingleton (HolomorphicOneForm X) :=
    subsingleton_holomorphicOneForm_of_classes X
  exact MeromorphicFunctionField.genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton
    X hSP

end JacobianChallenge

end
