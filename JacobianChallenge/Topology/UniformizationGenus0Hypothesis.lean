/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14ClassInstance
import JacobianChallenge.Manifold.HolomorphicEquiv

/-! # `UniformizationGenus0Hypothesis X` — the C3↔Item14 shared atom

`Item14ClassInstance.lean` ships the **disjunctive** uniformization
class

```
class FactUniformizationToRiemannSphere (X)
  out : (genus X = 0 ∨ Nonempty (X ≃ₜ StandardS2)) →
        Nonempty (HolomorphicEquiv X RiemannSphere)
```

which is what Item 14 needs (it has to handle both the `genus = 0`
*and* the topological-`S²` disjuncts). C3's genus-0 corner only ever
needs the left disjunct.

This file introduces the **weaker shared atom**

```
class UniformizationGenus0Hypothesis X
  out : genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)
```

and the bridge

```
instance : [FactUniformizationToRiemannSphere X] →
             UniformizationGenus0Hypothesis X
```

so that any caller who already had the stronger Item-14 class gets
the weaker C3-shared one automatically.

Unconditional Riemann-sphere instance is provided in this file via
`HolomorphicEquiv.refl`. Any caller (Item 14 forward, C3 genus-0
RR assemblies, the genus-0 case of `HasSurfaceClassificationData`)
should depend on this class rather than re-stating the implication
inline — that is the architectural payoff of naming the atom.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

/-- **Shared C3 ↔ Item-14 atom.**

The genus-0 corner of uniformization: every compact connected complex
1-manifold with `genus = 0` is biholomorphic to the Riemann sphere.

Strictly weaker than `FactUniformizationToRiemannSphere X` (which also
covers the topological-`S²` disjunct used by Item 14's reverse leg).
Use this class when you need only the `genus = 0` implication — that
is the case for the C3 genus-0 RR assemblies and for the easy half of
`HasSurfaceClassificationData` at genus 0. -/
class UniformizationGenus0Hypothesis (X : Type*)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop where
  out : JacobianChallenge.genus X = 0 →
    Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Bridge: the Item-14 disjunctive class implies the shared
genus-0-only class.** Any caller that already has
`[FactUniformizationToRiemannSphere X]` in scope automatically gets
`[UniformizationGenus0Hypothesis X]`, by feeding the `genus = 0`
hypothesis into the disjunctive Prop as `Or.inl`. -/
instance instUniformizationGenus0Hypothesis_of_FactUniformizationToRiemannSphere
    [FactUniformizationToRiemannSphere X] :
    UniformizationGenus0Hypothesis X where
  out hg := FactUniformizationToRiemannSphere.out (Or.inl hg)

/-- **Unconditional Riemann-sphere instance.** Trivial: `X = RS` is
biholomorphic to itself via `HolomorphicEquiv.refl`. (This also follows
via the `FactUniformizationToRiemannSphere RiemannSphere` instance +
the bridge above; we provide a direct discharge to keep the dependency
graph shallow.) -/
instance instUniformizationGenus0Hypothesis_RiemannSphere :
    UniformizationGenus0Hypothesis JacobianChallenge.RiemannSphere where
  out _ := ⟨HolomorphicEquiv.refl⟩

end JacobianChallenge

end
