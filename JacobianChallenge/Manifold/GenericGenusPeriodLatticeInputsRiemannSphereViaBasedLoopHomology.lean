/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromBasedLoopHomology
import JacobianChallenge.Manifold.BasedLoopHomologyFromBasedLoopsBound
import JacobianChallenge.Manifold.SmoothPathConnectedRiemannSphere
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances
import JacobianChallenge.Manifold.RiemannSphereGenus

set_option linter.unusedSectionVars false

/-! # `GenericGenusPeriodLatticeInputs` on `RiemannSphere` via the new
per-based-loop homology route

The existing unconditional construction
`genericGenusPeriodLatticeInputs_RiemannSphere`
(`GenericGenusPeriodLatticeInputsRiemannSphere.lean`) builds the
`GenericGenusPeriodLatticeInputs` structure for `RS` by discharging
`H1_spans_top_canonical` directly via
`subsingleton_canonical_H1_of_stokesBoundaries_eq_top
  stokesBoundaries_RS_eq_top` (the genus-0 quotient is trivial).

This file builds the SAME structure via the **new generic genus-≥1
route**: feed `BasedLoopHomologyDecompositionHypothesis` through
`GenericGenusPeriodLatticeInputs.ofBasedLoopHomology`. This validates
the new reduction (chips
`GenericGenusH1SpansTopFromLoopHomology` +
`GenericGenusPeriodLatticeInputsFromBasedLoopHomology` +
`BasedLoopHomologyFromBasedLoopsBound`) by reproducing the known
genus-0 RS closure as a special case.

The construction picks:
* `p₀ := (0 : ℂ) : RS`,
* `α := Classical.choice of smoothPathConnected_RiemannSphere p₀ x`,
* per-loop homology hypothesis: from `basedLoopHomologyDecompositionHypothesis_RS_holds`,
* the other three atomic inputs: as in
  `genericGenusPeriodLatticeInputs_RiemannSphere`.

## What this file ships

* `genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology`
* `nonempty_genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology`

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff
open Module Submodule

namespace JacobianChallenge

namespace RiemannSphere

/-- **`GenericGenusPeriodLatticeInputs` on `RS` via the
per-based-loop homology route.** Parallel of
`genericGenusPeriodLatticeInputs_RiemannSphere` discharged through
`GenericGenusPeriodLatticeInputs.ofBasedLoopHomology`. -/
noncomputable def genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology
    (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    GenericGenusPeriodLatticeInputs (X := RiemannSphere) basis := by
  classical
  -- Basepoint and based-path family from `smoothPathConnected_RiemannSphere`.
  set p₀ : RiemannSphere := ((0 : ℂ) : RiemannSphere) with hp₀_def
  have h_path : ∀ q : RiemannSphere,
      ∃ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere, γ.src = p₀ ∧ γ.tgt = q := by
    intro q
    exact smoothPathConnected_RiemannSphere p₀ q
  set α : RiemannSphere → SmoothPath 𝓘(ℝ, ℂ) RiemannSphere :=
    fun q => (h_path q).choose with hα_def
  have h_α_src : ∀ x, (α x).src = p₀ := fun q => (h_path q).choose_spec.1
  have h_α_tgt : ∀ x, (α x).tgt = x := fun q => (h_path q).choose_spec.2
  -- Empty `cycleGens` at genus 0.
  haveI hempty : IsEmpty (Fin (2 * JacobianChallenge.genus RiemannSphere)) := by
    rw [genus_RiemannSphere_eq_zero, Nat.mul_zero]; infer_instance
  -- Apply the new constructor.
  refine GenericGenusPeriodLatticeInputs.ofBasedLoopHomology
    basis hempty.elim linearIndependent_empty_type
    HolomorphicComponentsCanonicalClosed.of_subsingleton
    p₀ α h_α_src h_α_tgt ?_
  exact basedLoopHomologyDecompositionHypothesis_RS_holds hempty.elim p₀

/-- **Nonempty version of the parallel construction.** -/
theorem nonempty_genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology
    (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    Nonempty (GenericGenusPeriodLatticeInputs (X := RiemannSphere) basis) :=
  ⟨genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology basis⟩

end RiemannSphere

end JacobianChallenge

end
