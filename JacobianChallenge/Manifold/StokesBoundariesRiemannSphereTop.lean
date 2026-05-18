/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycleInStokesBoundariesOfBasedLoopsBound
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere
import JacobianChallenge.Manifold.SmoothPathConnectedRiemannSphere

set_option linter.unusedSectionVars false

/-! # `stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤` UNCONDITIONAL

Combines the cycle-decomposition headline
`cycle_in_stokesBoundaries_of_basedLoopsBound` with the unconditional
`basedSmoothLoopsBoundHypothesis_RS_holds` and the unconditional
`smoothPathConnected_RiemannSphere` to conclude that every smooth
1-cycle on the Riemann sphere lies in `stokesBoundaries`.

This closes the genus-0 corner of barrier (2)
`H1_spans_top_canonical` (the `canonicalH1 = ⊤` input to the
period-lattice bundle), at the SmoothCycle level.

## What this file ships

* `stokesBoundaries_RS_eq_top` — `stokesBoundaries 𝓘(ℝ, ℂ) RS = ⊤`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology

namespace JacobianChallenge

namespace RiemannSphere

/-- **`stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤`, unconditional.**

Every smooth 1-cycle on the Riemann sphere is a sum of smooth
2-simplex boundaries (i.e., lies in `stokesBoundaries`). -/
theorem stokesBoundaries_RS_eq_top :
    stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤ := by
  -- Pick a basepoint and extract a based-path family.
  set p₀ : RiemannSphere := ((0 : ℂ) : RiemannSphere) with hp₀_def
  have h_path : ∀ q : RiemannSphere,
      ∃ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere, γ.src = p₀ ∧ γ.tgt = q := by
    intro q
    exact smoothPathConnected_RiemannSphere p₀ q
  classical
  let α : RiemannSphere → SmoothPath 𝓘(ℝ, ℂ) RiemannSphere :=
    fun q => (h_path q).choose
  have h_α_src : ∀ q, (α q).src = p₀ := fun q => (h_path q).choose_spec.1
  have h_α_tgt : ∀ q, (α q).tgt = q := fun q => (h_path q).choose_spec.2
  -- Apply the cycle decomposition under
  -- `basedSmoothLoopsBoundHypothesis_RS_holds`.
  rw [AddSubgroup.eq_top_iff']
  intro c
  exact SmoothCycleDecomposition.cycle_in_stokesBoundaries_of_basedLoopsBound
    p₀ α h_α_src h_α_tgt (basedSmoothLoopsBoundHypothesis_RS_holds p₀) c

end RiemannSphere

end JacobianChallenge
