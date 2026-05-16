/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegrandContinuousAlongBetaFactors
import JacobianChallenge.Manifold.TraceFactorContinuousOnIcc01

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `IntegrandContinuousAlongBeta` from universal per-sheet + velocity

End-to-end composition combining

* the **factor-decomposed entry point**
  `integrandContinuousAlongBeta_of_factor_continuousOn`
  (`IntegrandContinuousAlongBetaFactors.lean`), and
* the **trace-factor `ContinuousOn (Icc 0 1)` lifting**
  `continuousOn_cotangentEquiv_fStarOmega_along_beta_Icc01`
  (`TraceFactorContinuousOnIcc01.lean`),

into a single API that discharges
`MeromorphicNonzero.IntegrandContinuousAlongBeta` from exactly two
plain continuity inputs:

1. **Universal per-sheet ContinuousOn** —
   `h_per_sheet_univ`: for every regular value `v₀`, the per-sheet
   cotangent-pullback covectors (through `cotangentEquiv`) are
   `ContinuousOn` the labelling nbhd at `v₀`.

2. **Velocity ContinuousOn (Icc 0 1)** —
   `h_vel`: the scalar `(mfderiv β s) 1` is `ContinuousOn (Icc 0 1)`
   as a ℂ-valued function.

Both inputs are plain `ContinuousOn` statements about concrete
functions — no fresh predicates, no dependent `if`.

Discharging (1) requires the forthcoming `cotangentPullbackAt`
smoothness/continuity chip (analytic core of `f-4`); discharging (2)
requires bundle-trivialised velocity continuity for smooth
`β : ℝ → RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`IntegrandContinuousAlongBeta` from per-sheet-univ + velocity inputs.** -/
theorem integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (h_per_sheet_univ :
      ∀ {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.regularValueSet),
        ∀ p ∈ (f.fiberFinset hv₀).attach,
          ContinuousOn
            (fun v : RiemannSphere =>
              (SmoothPath.cotangentEquiv
                (f.sheetCotPullback hnc
                  (f.mem_regularSet_of_preimage_regularValue hv₀
                    ((f.mem_fiberFinset_iff hv₀ p.val).mp p.property))
                  v om) : ℂ →L[ℝ] ℝ))
            (f.localFiberLabelingNbhd hnc hv₀))
    (h_vel : ContinuousOn
      (fun s : ℝ =>
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
            ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ) : ℂ))
      (Icc (0 : ℝ) 1)) :
    f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om := by
  -- Step 1: trace-factor `ContinuousOn (Icc 0 1)` from the universal per-sheet input.
  have h_trace :
      ContinuousOn
        (fun s : ℝ =>
          (SmoothPath.cotangentEquiv (f.fStarOmega hnc om (β s)) : ℂ →L[ℝ] ℝ))
        (Icc (0 : ℝ) 1) :=
    f.continuousOn_cotangentEquiv_fStarOmega_along_beta_Icc01
      hnc om hβ_smooth.continuous hβ_reg h_per_sheet_univ
  -- Step 2: combine trace + velocity via the factor-decomposed entry point.
  exact f.integrandContinuousAlongBeta_of_factor_continuousOn
    hnc hβ_smooth hβ_reg om h_trace h_vel

end MeromorphicNonzero

end JacobianChallenge

end
