/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromBasedSmoothLoopsBound
import JacobianChallenge.Manifold.PathPrimitiveGlobalSmoothFTC
import JacobianChallenge.Manifold.SmoothPathLocalConvex

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # `S2ImpliesGenus0` from `BasedSmoothLoopsBoundHypothesis` + admissibility

Composes `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis` (item 14
reverse leg with per-basis smoothness + FTC inputs) with the global
admissibility composition from
`Manifold/PathPrimitiveGlobalSmoothFTC.lean` to replace the per-basis
analytic hypotheses with a single uniform `PathPrimitiveAdmissibleChartCover`
hypothesis per basis element.

## What this file ships

* `s2ImpliesGenus0_of_bslb_and_admissibleChartCover` — `S2ImpliesGenus0 X`
  from two named inputs:
  * `h_bslb : SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`
    (period-lattice content);
  * `h_admit : SimplyConnectedSpace X → ∀ i, PathPrimitiveAdmissibleChartCover (b i)`
    (chart-cover analytic content).

The substantive content of the analytic side reduces to discharging
`ChartLocalPrimitiveSmoothExt` + `ChartLocalPrimitiveFTC` on each
chart of a chart cover (chart-local primitive smoothness + FTC, in
progress in `Manifold/ChartLocalPrimitiveSmoothness.lean`).

The smoothness witness `h_conn_from_sc` is discharged unconditionally
via `smoothPathConnected_of_preconnected` (from `[ConnectedSpace X]`,
which is in scope as a typeclass).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from `BasedSmoothLoopsBoundHypothesis` +
per-basis `PathPrimitiveAdmissibleChartCover`.**

Replaces the `h_smooth_b` + `h_ftc_b` per-basis analytic inputs of
`s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis` by the bundled
admissibility predicate
`PathPrimitiveAdmissibleChartCover (b i)`. The discharge uses
`pathPrimitive_contMDiff_of_admissible` and
`pathPrimitive_eval_eq_mfderiv_of_admissible` from
`Manifold/PathPrimitiveGlobalSmoothFTC.lean`. -/
theorem s2ImpliesGenus0_of_bslb_and_admissibleChartCover
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : SimplyConnectedSpace X →
      ∀ (i : ι), PathPrimitiveAdmissibleChartCover (b i)) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis (X := X) x₀ b
    (fun _ => smoothPathConnected_of_preconnected)
    h_bslb
    (fun hsc i =>
      pathPrimitive_contMDiff_of_admissible
        smoothPathConnected_of_preconnected x₀ (b i)
        (loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis
          (h_bslb hsc) (b i))
        (h_admit hsc i))
    (fun hsc i x =>
      pathPrimitive_eval_eq_mfderiv_of_admissible
        smoothPathConnected_of_preconnected x₀ (b i)
        (loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis
          (h_bslb hsc) (b i))
        (h_admit hsc i) x)

end JacobianChallenge

end
