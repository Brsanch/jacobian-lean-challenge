/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CriticalSetClosed
import JacobianChallenge.Manifold.CriticalSetDefinition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `a ∈ f.regularSet` from local injectivity at `a`

By definition, `a ∈ f.criticalSet` iff no nbhd of `a` has `f` injective
on it. Hence: if `∃ U ∈ 𝓝 a, Set.InjOn f.toRiemannSphere U`, then
`a ∉ f.criticalSet`, hence `a ∈ f.regularSet`
(`regularSet := criticalSet^c`).

No `sorry`, no `axiom`. -/

open Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **f.regularSet from local injectivity.** -/
theorem MeromorphicNonzero.mem_regularSet_of_local_injOn
    (f : MeromorphicNonzero X) {a : X}
    (h : ∃ U ∈ 𝓝 a, Set.InjOn f.toRiemannSphere U) :
    a ∈ f.regularSet := by
  -- `regularSet := { x : X | ∃ U ∈ 𝓝 x, Set.InjOn f.toRiemannSphere U }`.
  -- Direct membership.
  exact h

end JacobianChallenge
