/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromPrimitiveExistenceUnconditional
import JacobianChallenge.Manifold.LoopPeriodVanishesOfBasedSmoothLoopsBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # `S2ImpliesGenus0` from `BasedSmoothLoopsBoundHypothesis` + smoothness + FTC

Specialises `s2ImpliesGenus0_of_basisPathPrimitive` (item 14 reverse
leg) by discharging the per-basis-element `h_loop_b`
(`LoopPeriodVanishes`) input via
`loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`, which uses
chip D + 2-chain linearity.

Strictly **weaker** than `s2ImpliesGenus0_of_smoothlyNullBoundedHypothesis`
because `BasedSmoothLoopsBoundHypothesis` (every smooth loop's
singleCycle is in `stokesBoundaries`) is strictly weaker than
`SmoothlyNullBoundedHypothesis` (a single 2-simplex with constant
boundary on two faces). The reduction now needs:

* `h_bslb` — `SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis
  𝓘(ℝ, ℂ) X x₀` (universal 2-chain bounding of smooth loops).
* `h_smooth_b` — per-basis `ContMDiff ω (pathPrimitive ...)`.
* `h_ftc_b` — per-basis FTC at `eval`.

For `X = RiemannSphere`, the `h_bslb` input is **unconditional** in
tree (`basedSmoothLoopsBoundHypothesis_RS_holds`). For `X = ℂ`, same
via `_C_holds`. For general simply-connected smooth manifolds, the
content is classical 2-chain-bounding of loops (cellular approximation
+ 2-disc filling), which sits **between** "continuous null-homotopy"
(mathlib's `SimplyConnectedSpace`) and "smooth null-homotopy"
(Whitney smooth approximation).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from `BasedSmoothLoopsBoundHypothesis` +
per-basis smoothness + per-basis FTC.**

Replaces the `h_loop_b` input of
`s2ImpliesGenus0_of_basisPathPrimitive` by the universal
`BasedSmoothLoopsBoundHypothesis` (under `SimplyConnectedSpace X`),
applied via `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`. -/
theorem s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_conn_from_sc : SimplyConnectedSpace X → SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)))
    (h_ftc_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)) x) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_basisPathPrimitive (X := X) x₀ b h_conn_from_sc
    (fun hsc i =>
      loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis
        (h_bslb hsc) (b i))
    h_smooth_b h_ftc_b

end JacobianChallenge

end
