/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveSubsingletonReduction
import JacobianChallenge.Manifold.LoopPeriodVanishesOfBasedSmoothLoopsBound
import JacobianChallenge.Manifold.SmoothPathLocalConvex
import JacobianChallenge.Topology.S2ImpliesGenus0FromSubsingletonHypothesis

set_option linter.unusedSectionVars false

/-! # `Subsingleton (HolomorphicOneForm X)` from BSLB + path-primitive analytic data

The reverse leg of item 14 has, up to now, threaded through three named
inputs supplied separately:

1. `AllLoopsVanish x₀` — every holomorphic 1-form's period vanishes
   along every smooth based loop at `x₀`.
2. `PathPrimitiveSmoothness h_conn x₀` — the path-primitive of every
   1-form is `ContMDiff ω` in its endpoint.
3. `PathPrimitiveFTC h_conn x₀` — the path-primitive's manifold
   derivative recovers the 1-form's `eval` pointwise.

The first input is structurally derivable from
`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` via chip D's
unconditional `HolomorphicStokesHypothesis` lifted to 2-chains
(`loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`, in
`Manifold/LoopPeriodVanishesOfBasedSmoothLoopsBound.lean`). The
smooth-path-connectedness witness `h_conn` is also unconditional for
preconnected `X` via `smoothPathConnected_of_preconnected` in
`Manifold/SmoothPathLocalConvex.lean`.

This file consolidates: **under `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`
plus path-primitive smoothness + FTC against the auto-discharged
`smoothPathConnected_of_preconnected` witness, `Subsingleton
(HolomorphicOneForm X)` follows.**

Composing with `s2ImpliesGenus0_from_subsingletonOfSimplyConnected` and
the unconditional `simplyConnectedS2_holds` then yields `S2ImpliesGenus0
X` from a clean 3-input shape: BSLB + smoothness + FTC. This drops the
prior `AllLoopsVanish` from the consumer's input list, factoring the
substantive smooth-Hurewicz content of the reverse leg into the single
`BasedSmoothLoopsBoundHypothesis` named hypothesis (which is in turn
unconditional on `RiemannSphere` via
`basedSmoothLoopsBoundHypothesis_RS_holds`).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## `AllLoopsVanish` from BSLB -/

/-- **Universal `AllLoopsVanish` from `BasedSmoothLoopsBoundHypothesis`.**

Lifts `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis` to the
universally-quantified-over-`om` form
`AllLoopsVanish x₀ := ∀ om, LoopPeriodVanishes om x₀`. The proof is
direct: for each `om`, the universal BSLB chip applies. -/
theorem allLoopsVanish_of_basedSmoothLoopsBoundHypothesis
    {x₀ : X} (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    AllLoopsVanish (X := X) x₀ := fun om =>
  loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis h_bslb om

/-! ## `Subsingleton (HolomorphicOneForm X)` from BSLB + smoothness + FTC -/

/-- **`Subsingleton (HolomorphicOneForm X)` from
`BasedSmoothLoopsBoundHypothesis` + path-primitive smoothness + FTC.**

Composes:
* `allLoopsVanish_of_basedSmoothLoopsBoundHypothesis` —
  `AllLoopsVanish x₀` from BSLB;
* `smoothPathConnected_of_preconnected` — auto-discharged
  smooth-path-connectedness witness on preconnected `X`;
* `subsingleton_of_pathPrimitive_hypotheses` — the existing assembly
  in `Manifold/PrimitiveSubsingletonReduction.lean`.

The two remaining inputs are the analytic-content per-1-form
smoothness + FTC of the path-primitive. -/
theorem subsingleton_of_BSLB_and_pathPrimitive
    (x₀ : X) (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth : PathPrimitiveSmoothness
      (smoothPathConnected_of_preconnected (X := X)) x₀)
    (h_ftc : PathPrimitiveFTC
      (smoothPathConnected_of_preconnected (X := X)) x₀) :
    Subsingleton (HolomorphicOneForm X) :=
  subsingleton_of_pathPrimitive_hypotheses
    (smoothPathConnected_of_preconnected (X := X)) x₀
    (allLoopsVanish_of_basedSmoothLoopsBoundHypothesis h_bslb)
    h_smooth h_ftc

/-! ## `HolomorphicOneFormSubsingletonOfSimplyConnected` from the same -/

/-- **`HolomorphicOneFormSubsingletonOfSimplyConnected X` from
`BasedSmoothLoopsBoundHypothesis` (under SimplyConnectedSpace) +
path-primitive smoothness + FTC.**

The SimplyConnectedSpace hypothesis is used only to discharge BSLB +
the analytic hypotheses (which are classically expected to follow from
simple-connectedness, hence are stated parameterized on it). -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_BSLB_and_pathPrimitive
    (x₀ : X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth : SimplyConnectedSpace X →
      PathPrimitiveSmoothness
        (smoothPathConnected_of_preconnected (X := X)) x₀)
    (h_ftc : SimplyConnectedSpace X →
      PathPrimitiveFTC
        (smoothPathConnected_of_preconnected (X := X)) x₀) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X := fun h_sc =>
  subsingleton_of_BSLB_and_pathPrimitive x₀ (h_bslb h_sc)
    (h_smooth h_sc) (h_ftc h_sc)

/-! ## `S2ImpliesGenus0` from the same -/

/-- **`S2ImpliesGenus0 X` from `BasedSmoothLoopsBoundHypothesis` (under
SimplyConnectedSpace) + path-primitive smoothness + FTC, with
`SimplyConnectedS2` dropped.**

Composes the previous theorem with
`s2ImpliesGenus0_from_subsingletonOfSimplyConnected` and the
unconditional `simplyConnectedS2_holds`.

Net effect: the reverse leg of Item 14 (`S2ImpliesGenus0 X`) reduces
to **three named classical inputs** packaged as predicates on
simply-connected `X`:

* `h_bslb` — every smooth based loop bounds (smooth Hurewicz, weaker
  than smooth Poincaré: only `single γ ∈ stokesBoundaries` is required,
  not a single 2-simplex with constant boundary on two faces);
* `h_smooth` — path-primitive smoothness in the endpoint;
* `h_ftc` — path-primitive FTC.

All three are textbook classical content owed at the mathlib pin. -/
theorem s2ImpliesGenus0_of_BSLB_and_pathPrimitive
    (x₀ : X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth : SimplyConnectedSpace X →
      PathPrimitiveSmoothness
        (smoothPathConnected_of_preconnected (X := X)) x₀)
    (h_ftc : SimplyConnectedSpace X →
      PathPrimitiveFTC
        (smoothPathConnected_of_preconnected (X := X)) x₀) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_from_subsingletonOfSimplyConnected X
    (holomorphicOneFormSubsingletonOfSimplyConnected_of_BSLB_and_pathPrimitive
      x₀ h_bslb h_smooth h_ftc)

end JacobianChallenge

end
