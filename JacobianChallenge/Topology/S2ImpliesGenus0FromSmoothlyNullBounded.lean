/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromPrimitiveExistenceUnconditional
import JacobianChallenge.Manifold.SmoothlyNullBoundedLoopPeriod

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # `S2ImpliesGenus0` from smooth null-bounding + smoothness + FTC

Specialises `s2ImpliesGenus0_of_basisPathPrimitive` (item 14 reverse
leg) by discharging the `h_loop_b` (per-basis-element
`LoopPeriodVanishes`) input via
`loopPeriodVanishes_of_smoothlyNullBoundedHypothesis` (which uses chip
D's unconditional `HolomorphicStokesHypothesis`).

The resulting reduction needs only **three universal inputs** at
each `SimplyConnectedSpace X`:

* `h_snbh` — `SimplyConnectedSpace X → SmoothlyNullBoundedHypothesis X x₀`
  (universal smooth-Poincaré-disc filling).
* `h_smooth_b` — per-basis `ContMDiff ω (pathPrimitive ...)`.
* `h_ftc_b` — per-basis FTC at `eval`.

The first input is the substantive new residual content; it isolates
the smooth-approximation gap from the rest of the chain.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from smooth null-bounding + per-basis smoothness
+ per-basis FTC.**

Replaces the `h_loop_b` input of
`s2ImpliesGenus0_of_basisPathPrimitive` by the universal smooth
null-bounding hypothesis `h_snbh`, applied via
`loopPeriodVanishes_of_smoothlyNullBoundedHypothesis`. -/
theorem s2ImpliesGenus0_of_smoothlyNullBoundedHypothesis
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_conn_from_sc : SimplyConnectedSpace X → SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (h_snbh : SimplyConnectedSpace X → SmoothlyNullBoundedHypothesis X x₀)
    (h_smooth_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)))
    (h_ftc_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)) x) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_basisPathPrimitive (X := X) x₀ b h_conn_from_sc
    (fun hsc i =>
      loopPeriodVanishes_of_smoothlyNullBoundedHypothesis
        (h_snbh hsc) (b i))
    h_smooth_b h_ftc_b

end JacobianChallenge

end
