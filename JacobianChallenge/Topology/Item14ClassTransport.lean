/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14ClassInstance
import JacobianChallenge.Manifold.HolomorphicEquivGenusInvariance

set_option diagnostics.threshold 100

/-! # Transport of `FactUniformizationToRiemannSphere` under biholomorphisms

zz316 introduced `FactUniformizationToRiemannSphere X` and discharged
the typeclass for `X = RiemannSphere` and for any `X` with a known
biholomorphism with `RiemannSphere`. This file ships the *transport*
direction: if `[FactUniformizationToRiemannSphere Y]` and we have
`e : HolomorphicEquiv X Y`, then `FactUniformizationToRiemannSphere X`
follows.

Combined with zz310's `HolomorphicEquiv.genus_eq` (genus invariance)
and zz308's `pullbackLinearEquiv` machinery, the typeclass propagates
through arbitrary biholomorphism chains.

## Why this matters for item 14

It encodes the algebraic invariance of the open hypothesis: if any one
member of a biholomorphism class satisfies uniformization, the entire
class does. So downstream code only ever needs to discharge the
hypothesis on a *canonical representative* of the biholomorphism class.

This is the closest we can get at the pinned mathlib commit toward
"strict closure of item 14" without uniformization itself: the
hypothesis is now stable under all the manifold-categorical operations
we can prove.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Transport of `UniformizationToRiemannSphere` through a
biholomorphism.** Given `e : HolomorphicEquiv X Y` and
`hY : UniformizationToRiemannSphere Y`, we obtain
`UniformizationToRiemannSphere X` by composing.

Proof: from a witness in either disjunct on the X side, transport via
`e` to the Y side (using `genus_eq` for the genus disjunct, and
`e.toHomeomorph.trans` for the topological-sphere disjunct), apply `hY`,
and post-compose the resulting biholomorphism with `e` itself. -/
theorem uniformizationToRiemannSphere_of_HolomorphicEquiv
    (e : HolomorphicEquiv X Y)
    (hY : UniformizationToRiemannSphere Y) :
    UniformizationToRiemannSphere X := by
  intro h
  rcases h with hg | hHomeo
  · -- genus X = 0 case: transport to genus Y = 0 via e.genus_eq.symm
    have hgY : JacobianChallenge.genus Y = 0 := e.genus_eq.symm.trans hg
    obtain ⟨f⟩ := hY (Or.inl hgY)
    exact ⟨e.trans f⟩
  · -- Nonempty (X ≃ₜ S²) case: transport to Nonempty (Y ≃ₜ S²) via e.symm
    obtain ⟨hXS2⟩ := hHomeo
    have hHomeoY : Nonempty (Y ≃ₜ StandardS2) :=
      ⟨e.toHomeomorph.symm.trans hXS2⟩
    obtain ⟨f⟩ := hY (Or.inr hHomeoY)
    exact ⟨e.trans f⟩

/-- **Class-level transport.** Not an `instance` because `Y` cannot be
synthesised from `X` alone; supply explicitly at the call site. -/
theorem FactUniformizationToRiemannSphere.of_HolomorphicEquiv
    (e : HolomorphicEquiv X Y) [hY : FactUniformizationToRiemannSphere Y] :
    FactUniformizationToRiemannSphere X where
  out := uniformizationToRiemannSphere_of_HolomorphicEquiv e hY.out

/-- **Both-direction transport.** Biholomorphic spaces have the same
`UniformizationToRiemannSphere` status. Useful for callers that want
to normalise their argument to a canonical representative of the
biholomorphism class. -/
theorem uniformizationToRiemannSphere_iff_of_HolomorphicEquiv
    (e : HolomorphicEquiv X Y) :
    UniformizationToRiemannSphere X ↔ UniformizationToRiemannSphere Y := by
  refine ⟨fun hX => ?_, fun hY => ?_⟩
  · exact uniformizationToRiemannSphere_of_HolomorphicEquiv e.symm hX
  · exact uniformizationToRiemannSphere_of_HolomorphicEquiv e hY

end JacobianChallenge

end
