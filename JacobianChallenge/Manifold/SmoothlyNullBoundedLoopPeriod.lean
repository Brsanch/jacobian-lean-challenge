/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothNullBounding

set_option linter.unusedSectionVars false

/-! # Universal `LoopPeriodVanishes` from universal `SmoothNullBounding`

A universally-quantified version of `loopPeriodVanishes_of_smoothNullBounding`:
if every smooth based loop at `x₀` is smoothly null-bounded, then
every holomorphic 1-form's period vanishes along every such loop —
i.e., `LoopPeriodVanishes om x₀` holds for every `om`.

The substantive open content factors cleanly: closing the named
`SmoothlyNullBoundedHypothesis X x₀` (every smooth based loop
smoothly bounds a 2-simplex with constant boundary on two faces)
delivers universal `LoopPeriodVanishes`, which is one of the
per-basis-element analytic inputs of `S2ImpliesGenus0` (item 14
reverse leg, per `s2ImpliesGenus0_of_basisPathPrimitive`).

## What ships

* `SmoothlyNullBoundedHypothesis X x₀` — named universal predicate.
* `loopPeriodVanishes_of_smoothlyNullBoundedHypothesis` — `∀ om,
  LoopPeriodVanishes om x₀` from the universal hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SmoothlyNullBoundedHypothesis X x₀`** — every smooth based loop
at `x₀` is `SmoothNullBounding` at `x₀`.

Classically, this is "smooth Poincaré disc filling on a smoothly
simply-connected manifold". Discharging it for compact connected
complex 1-manifolds X with `SimplyConnectedSpace X` requires smooth
approximation (Whitney) of continuous null-homotopies. -/
def SmoothlyNullBoundedHypothesis (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] (x₀ : X) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X, γ.src = x₀ → γ.tgt = x₀ →
    SmoothNullBounding γ x₀

/-- **Universal `LoopPeriodVanishes` from `SmoothlyNullBoundedHypothesis`.**

For every holomorphic 1-form `om`, `LoopPeriodVanishes om x₀` holds
under the universal null-bounding hypothesis. Direct application of
`loopPeriodVanishes_of_smoothNullBounding` per loop. -/
theorem loopPeriodVanishes_of_smoothlyNullBoundedHypothesis
    {x₀ : X} (h : SmoothlyNullBoundedHypothesis X x₀)
    (om : HolomorphicOneForm X) :
    LoopPeriodVanishes om x₀ := by
  intro γ h_src h_tgt
  exact loopPeriodVanishes_of_smoothNullBounding
    h_src h_tgt (h γ h_src h_tgt) om

end JacobianChallenge

end
