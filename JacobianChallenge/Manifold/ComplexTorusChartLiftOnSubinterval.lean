/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusLocalSmoothLift
import JacobianChallenge.Manifold.ComplexTorusLebesgueChartCover

set_option linter.unusedSectionVars false

/-! # Chart-symm-composition as a smooth lift on a sub-interval

Pairs with `ComplexTorusLebesgueChartCover`. Given a sub-interval
`Icc a b ⊆ ℝ` on which `γ.ambient` maps into the chart source at
anchor `x : ℂ`, the chart-symm composition
`t ↦ (localChart L _ x).symm (γ.ambient t)` is a **smooth ℂ-valued lift**
of `γ.ambient` on `Icc a b`:

  * `ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞` on `Icc a b`,
  * `mkQ ∘ chartLift = γ.ambient` pointwise on `Icc a b`.

This is the per-piece building block for the global smooth-lift
construction `SmoothPathLiftHypothesisTorus L`: combined with the
`Fin N` partition from `ComplexTorusLebesgueChartCover` and a
cumulative lattice shift to make the pieces agree at the seams, the
per-piece smooth lifts assemble into a global smooth lift `ℝ → ℂ`.

## What this file ships

* `ComplexTorus.chartLift_contMDiffOn_subinterval` — smoothness on the
  sub-interval.

* `ComplexTorus.mkQ_chartLift_on_subinterval` — `mkQ ∘ chartLift =
  γ.ambient` on the sub-interval.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness of the chart-symm-composition on a sub-interval -/

/-- **Chart-symm composition is `ContMDiffOn` on a sub-interval** where
`γ.ambient` maps into the chart source at the anchor. -/
theorem chartLift_contMDiffOn_subinterval
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x : ℂ) {a b : ℝ}
    (h_in : ∀ t ∈ Set.Icc a b,
        γ.ambient t ∈ (localChart L (discRadius_separates L) x).symm.source) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (localChart L (discRadius_separates L) x).symm (γ.ambient t))
      (Set.Icc a b) := by
  -- chartComp_contMDiffOn gives smoothness on the FULL chart-source preimage;
  -- restrict via `ContMDiffOn.mono` using the containment from h_in.
  have h_full := chartComp_contMDiffOn L γ x
  have h_subset : Set.Icc a b ⊆
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) x).symm.source := by
    intro t ht; exact h_in t ht
  exact h_full.mono h_subset

/-! ## `mkQ ∘ chartLift = γ.ambient` on the sub-interval -/

/-- **The chart-symm composition is a lift of `γ.ambient` on the
sub-interval.** -/
theorem mkQ_chartLift_on_subinterval
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x : ℂ) {a b : ℝ}
    (h_in : ∀ t ∈ Set.Icc a b,
        γ.ambient t ∈ (localChart L (discRadius_separates L) x).symm.source) :
    ∀ t ∈ Set.Icc a b,
      L.mkQ ((localChart L (discRadius_separates L) x).symm (γ.ambient t)) =
        γ.ambient t := by
  intro t ht
  -- (localChart L _ x).right_inv on the chart-symm.source.
  exact (localChart L (discRadius_separates L) x).right_inv (h_in t ht)

end ComplexTorus

end JacobianChallenge

end
