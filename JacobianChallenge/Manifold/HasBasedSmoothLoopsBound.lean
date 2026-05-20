/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureSubsingleton
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false

/-! # `HasBasedSmoothLoopsBound X` — typeclass wrapper for BSLB

A typeclass form of `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀` for
some basepoint `p₀`. Allows the existing per-basepoint BSLB theorems to
fire as instance resolutions.

The RS instance is unconditional via
`basedSmoothLoopsBoundHypothesis_RS_holds`.

Together with `HasJacobianAnalyticStructure.of_subsingleton_and_BSLB`,
the chain `[Subsingleton ω] + [HasBSLB X] ⟹ HasJacobianAnalyticStructure X`
becomes typeclass-resolvable.

## What this file ships

* `HasBasedSmoothLoopsBound X` — Prop class wrapping
  `∃ p₀, BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀`.
* `instHasBasedSmoothLoopsBound_RiemannSphere` — unconditional RS
  instance.
* `HasJacobianAnalyticStructure.of_subsingleton_and_HasBSLB` —
  derive `HasJacobianAnalyticStructure X` from
  `[Subsingleton ω]` + `[HasBasedSmoothLoopsBound X]`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasBasedSmoothLoopsBound X` class.** Asserts existence of a
basepoint `p₀ : X` at which `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀`
holds. -/
class HasBasedSmoothLoopsBound (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- A basepoint together with the BSLB witness at that basepoint. -/
  out : ∃ p₀ : X, BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀

/-- **Unconditional RS instance.** Discharged via the in-tree
`basedSmoothLoopsBoundHypothesis_RS_holds` for any basepoint. -/
instance instHasBasedSmoothLoopsBound_RiemannSphere :
    HasBasedSmoothLoopsBound RiemannSphere := by
  refine ⟨?_⟩
  -- ConnectedSpace.toNonempty gives a basepoint.
  haveI : Nonempty RiemannSphere := ConnectedSpace.toNonempty
  refine ⟨Classical.arbitrary RiemannSphere, ?_⟩
  exact RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds _

/-- **`HasJacobianAnalyticStructure X` from `[Subsingleton ω]` + the
typeclass form of BSLB.** Wraps
`HasJacobianAnalyticStructure.of_subsingleton_and_BSLB` with the
existence of a basepoint extracted via `Classical.choose` on the BSLB
class. -/
theorem HasJacobianAnalyticStructure.of_subsingleton_and_HasBSLB
    [Subsingleton (HolomorphicOneForm X)]
    [hBSLB : HasBasedSmoothLoopsBound X] :
    HasJacobianAnalyticStructure X :=
  let ⟨p₀, h⟩ := Classical.choice ⟨hBSLB.out⟩
  HasJacobianAnalyticStructure.of_subsingleton_and_BSLB p₀ h

end JacobianChallenge

end
