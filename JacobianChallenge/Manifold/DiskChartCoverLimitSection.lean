/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverCLMLimit
import JacobianChallenge.Manifold.DiskChartCoverLimitAnalytic

set_option diagnostics.threshold 100

/-! # Limit section's underlying function

Defines `limitSectionToFun : ∀ y : X, CotangentSpace 𝓘(ℂ) y` as the
pointwise CLM limit from chip 5e, via `Classical.choose`.

Establishes the convergence property: for every `y ∈ X`, the sequence
`om_n (ψ k).toFun y` converges to `limitSectionToFun ... y` in the
cotangent fibre.

The smoothness verification (making this into an honest
`HolomorphicOneForm X`) is a follow-up chip — it uses the chart-x-frame
analyticity (chip 5f) plus the section-coord bridge.

## Main definitions

* `DiskChartCover.limitSectionToFun` — the pointwise CLM limit
  function (∀ y : X, CotangentSpace 𝓘(ℂ) y).

## Main results

* `DiskChartCover.limitSectionToFun_tendsto` — pointwise convergence.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The pointwise CLM limit function in the cotangent fibre at every
`y ∈ X`. -/
noncomputable def limitSectionToFun
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    (y : X) : CotangentSpace 𝓘(ℂ) y :=
  (section_value_tendsto cover om_n h_diag y).choose

/-- **Pointwise convergence to the limit section's value.** -/
theorem limitSectionToFun_tendsto
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    (y : X) :
    Tendsto (fun k => (om_n (ψ k)).toFun y) atTop
      (𝓝 (limitSectionToFun cover om_n h_diag y)) :=
  (section_value_tendsto cover om_n h_diag y).choose_spec

end DiskChartCover

end JacobianChallenge

end
