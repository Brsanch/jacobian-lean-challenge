/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveAdmissibleChartCoverMaxUnconditional
import JacobianChallenge.Manifold.SmoothPathLocalConvex
import JacobianChallenge.Topology.SubsingletonFromPrimitiveExistence
import JacobianChallenge.Topology.SimplyConnectedS2Unconditional

set_option linter.unusedSectionVars false

/-! # `S2ImpliesGenus0 X` from period-vanishing on simply-connected X

Final composition of the chartLocalPrimitive maxAtlas cascade
(steps 1–6, landed in this session). Reduces `S2ImpliesGenus0 X` on
arbitrary compact connected complex 1-manifold X to one named classical
input:

* **period-vanishing on simply-connected X** — for every holomorphic
  1-form `om` and every basepoint `x₀`, every smooth loop at `x₀` has
  zero `complexChainPeriod` against `om` (i.e. `LoopPeriodVanishes om x₀`).

This is the classical Stokes-on-disks content: on a simply-connected
manifold every loop is null-homotopic; a closed 1-form (which a
holomorphic 1-form is) has zero integral over null-homotopic loops by
Stokes on the homotopy disk. The actual chart-by-chart monodromy /
homotopy-Stokes argument is the remaining classical content beyond
this cascade — independent of the chartLocalPrimitive analytic chain.

## What the cascade contributes

This file shows that the *analytic* side of the
`HolomorphicOneFormSubsingletonOfSimplyConnected` arc — i.e. the
existence of a globally-smooth primitive `F` with `mfderiv F = om.eval`
— is now unconditional on arbitrary X, given the period-vanishing
hypothesis. The cascade payoff
(`pathPrimitive_contMDiff_unconditional` +
`pathPrimitive_eval_eq_mfderiv_unconditional`) supplies both
ContMDiff ω of `pathPrimitive om` and the FTC at every point, with no
admissibility or convex-target assumptions on the chart cover.

## What this file ships

* `pathPrimitive_isSmoothPrimitive_unconditional` — under
  `LoopPeriodVanishes om x₀`, `pathPrimitive om` is a globally-smooth
  function `X → ℂ` with `mfderiv = om.eval`. Packaged in the existential
  form consumed by the in-tree primitive-existence chain.
* `s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected` — closes
  `S2ImpliesGenus0 X` from the named period-vanishing hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`pathPrimitive om` is a smooth primitive of `om`** under
`LoopPeriodVanishes om x₀`, on arbitrary X. Packaged in the existential
form expected by `subsingleton_of_primitiveExistence`. -/
theorem pathPrimitive_isSmoothPrimitive_unconditional
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀) :
    ∃ F : X → ℂ,
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
        ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x := by
  have h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X :=
    smoothPathConnected_of_preconnected
  exact ⟨pathPrimitive h_conn x₀ om,
    pathPrimitive_contMDiff_unconditional h_conn x₀ om h_loop,
    fun x => pathPrimitive_eval_eq_mfderiv_unconditional h_conn x₀ om h_loop x⟩

/-- **`S2ImpliesGenus0 X` from period-vanishing on simply-connected X.**

The cascade reduces Item 14's reverse leg (`S2ImpliesGenus0 X`) to a
single classical input: period-vanishing of holomorphic 1-forms on
simply-connected compact connected complex 1-manifolds, parameterised
by an arbitrary basepoint `x₀`.

Composition:
* `simplyConnectedS2_holds` (unconditional, from
  `Topology/SimplyConnectedS2Unconditional.lean`) discharges
  `SimplyConnectedS2`.
* The cascade discharges the primitive-existence content of the
  `HolomorphicOneFormSubsingletonOfSimplyConnected` arc.
* `s2ImpliesGenus0_of_primitiveExistence` (in-tree) wires the pieces
  through `s2ImpliesGenus0_from_simplyConnected`. -/
theorem s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected
    (x₀ : X)
    (h_loop_vanishes : SimplyConnectedSpace X →
      ∀ om : HolomorphicOneForm X, LoopPeriodVanishes om x₀) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_primitiveExistence simplyConnectedS2_holds <| fun h_sc om =>
    pathPrimitive_isSmoothPrimitive_unconditional x₀ om
      (h_loop_vanishes h_sc om)

end JacobianChallenge

end
