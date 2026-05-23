/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentFromHolomorphicEquivRS
import JacobianChallenge.Topology.UniformizationGenus0Hypothesis

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` from `[UniformizationGenus0Hypothesis X]` + `genus X = 0`

Composes the typeclass `UniformizationGenus0Hypothesis X` (the
genus-0 corner of uniformization) with this session's
`_of_holomorphicEquiv_RiemannSphere` chip.

The benefit over the direct biholomorphism input: any X with a
universal-class-level `[FactUniformizationToRiemannSphere X]` (or even
the weaker `[UniformizationGenus0Hypothesis X]`) plus a `genus = 0`
proof gets HJCC unconditionally.

## What ships

* `HasJacobianClassicalContent.of_uniformizationGenus0` — HJCC X from
  the typeclass + genus = 0.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJCC from `[UniformizationGenus0Hypothesis X]` + `genus X = 0`.** -/
theorem HasJacobianClassicalContent.of_uniformizationGenus0
    [UniformizationGenus0Hypothesis X]
    (h_genus : JacobianChallenge.genus X = 0) :
    HasJacobianClassicalContent X := by
  obtain ⟨φ⟩ := UniformizationGenus0Hypothesis.out h_genus
  exact HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere φ

end JacobianChallenge

end
