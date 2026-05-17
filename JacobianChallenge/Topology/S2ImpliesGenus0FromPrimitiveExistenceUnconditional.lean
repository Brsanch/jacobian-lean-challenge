/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SubsingletonFromPrimitiveExistence
import JacobianChallenge.Topology.SimplyConnectedS2Unconditional
import JacobianChallenge.Topology.S2ImpliesGenus0FromSubsingletonHypothesis
import JacobianChallenge.Manifold.PathPrimitiveBasisFTC
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-! # `S2ImpliesGenus0 X` from primitive existence, with `SimplyConnectedS2` dropped

The chip `s2ImpliesGenus0_of_primitiveExistence` in
`SubsingletonFromPrimitiveExistence.lean` reduces the reverse leg of
Item 14 to two inputs:

* `SimplyConnectedS2` — now **unconditional** via `simplyConnectedS2_holds`.
* A primitive-existence hypothesis on simply-connected `X`.

This file drops the first hypothesis (it's discharged internally) and
provides a basis-factored entry point: the primitive-existence
hypothesis can be supplied **per basis element** of `HolomorphicOneForm
X` via the `pathPrimitiveSmoothness_of_basis` /
`pathPrimitiveFTC_of_basis` / `allLoopsVanish_of_basis` reductions.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from primitive existence, with `SimplyConnectedS2`
dropped.** Replaces `s2ImpliesGenus0_of_primitiveExistence`'s
`h_S2_sc : SimplyConnectedS2` premise by the unconditional
`simplyConnectedS2_holds`. -/
theorem s2ImpliesGenus0_of_primitiveExistence_uncond
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
              ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_primitiveExistence (X := X)
    simplyConnectedS2_holds h_primitive_exists

/-- **`HolomorphicOneFormSubsingletonOfSimplyConnected X` from basis-level
pathPrimitive data.** Given a ℂ-basis of `HolomorphicOneForm X`
(available unconditionally via item 1) and the three per-basis-element
analytic hypotheses (`LoopPeriodVanishes`, `ContMDiff ω` of
`pathPrimitive`, FTC at `eval`), assemble the named
`HolomorphicOneFormSubsingletonOfSimplyConnected X` predicate via the
basis-reductions `allLoopsVanish_of_basis`,
`pathPrimitiveSmoothness_of_basis`, and `pathPrimitiveFTC_of_basis`. -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_basisPathPrimitive
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_conn_from_sc : SimplyConnectedSpace X → SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (h_loop_b : SimplyConnectedSpace X → ∀ i, LoopPeriodVanishes (b i) x₀)
    (h_smooth_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)))
    (h_ftc_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)) x) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X := by
  intro hsc
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  exact subsingleton_of_pathPrimitive_hypotheses (h_conn_from_sc hsc) x₀
    (allLoopsVanish_of_basis b (h_loop_b hsc))
    (pathPrimitiveSmoothness_of_basis b (h_conn_from_sc hsc) x₀
      (h_smooth_b hsc))
    (pathPrimitiveFTC_of_basis b (h_conn_from_sc hsc) x₀
      (h_smooth_b hsc) (h_ftc_b hsc))

/-- **Full-arc composition: `S2ImpliesGenus0 X` from basis-level
pathPrimitive data, with `SimplyConnectedS2` dropped.** Composes
`holomorphicOneFormSubsingletonOfSimplyConnected_of_basisPathPrimitive`
with `s2ImpliesGenus0_from_subsingletonOfSimplyConnected` (which itself
uses `simplyConnectedS2_holds` internally).

This is the **finest-grained reduction** of `S2ImpliesGenus0 X` to
per-basis-element analytic statements: given a ℂ-basis of
`HolomorphicOneForm X` (size `genus X`, available via item 1), the
single named external input is `2g + g = 3g` per-basis-element analytic
assertions (one `LoopPeriodVanishes`, one `ContMDiff ω
(pathPrimitive)`, one FTC per basis element). -/
theorem s2ImpliesGenus0_of_basisPathPrimitive
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_conn_from_sc : SimplyConnectedSpace X → SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (h_loop_b : SimplyConnectedSpace X → ∀ i, LoopPeriodVanishes (b i) x₀)
    (h_smooth_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)))
    (h_ftc_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)) x) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_from_subsingletonOfSimplyConnected X
    (holomorphicOneFormSubsingletonOfSimplyConnected_of_basisPathPrimitive
      X x₀ b h_conn_from_sc h_loop_b h_smooth_b h_ftc_b)

end JacobianChallenge

end
