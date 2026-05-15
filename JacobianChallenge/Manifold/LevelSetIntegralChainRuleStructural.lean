/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandPullback
import JacobianChallenge.Manifold.SumSourceFiberIntegrandPullback
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetIntegrate

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Structural chain-rule identity for the level-set chain integral (segment)

For `t ∈ Ioo 0 δ` (the sub-interval from
`sourceFiberPath_ambient_eq_sheet_g_locally`) and assuming per-fiber-point
realified smoothness of each `sheet_p.g` at `β (σ t)`, the level-set
chain's integrand (as a Finset-sum over `sourceFiber.attach`) collapses
to:

```
∑_{p ∈ sourceFiber} integrand (sourceFiberPath p) ω t
  = applyCotangent
      (∑_{p ∈ sourceFiber} cotangentPullbackAt sheet_p.g (β(σ t)) ω)
      (mfderiv β (σ t) (mfderiv σ t 1))
```

Combining the per-fiber-point chip
`sourceFiberPath_integrand_eq_cotangentPullbackAt_apply` with the sum
distribution chip `applyCotangent_sourceFiber_sum_cotangentPullbackAt`.

**This is the chain-rule structural identity on a sub-interval**. The
remaining segments are:

1. The sum `∑_p cotangentPullbackAt sheet_p.g (β(σ t)) ω` corresponds to
   `traceAt(ω)(β(σ t))` via the local-sheet bijection sourceFiber ↔
   `f⁻¹(β(σ t))` (next chip / future work).

2. Gluing across the Lebesgue subdivision
   (`exists_subdivision_hurwitzPatching`) lifts the sub-interval
   identity to `[0, 1]`.

3. The `σ`-reparametrisation reduces `∫₀¹` to `∫₀¹` in the original
   `β` parametrisation.

4. The "global integral of `traceAt(ω)` along β is in lattice" — the
   residue-theorem-on-ℙ¹-for-meromorphic-1-forms named hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-fiber-point integrand sum collapses to a single
`applyCotangent`.** This is the structural backbone, taking `t` as
input + per-fiber-point realified-smoothness as input. -/
theorem sum_sourceFiber_integrand_chain_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t : ℝ}
    (h_per_fiber : ∀ p : { x : X //
        x ∈ f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
      (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)).integrand om t
        = SmoothPath.applyCotangent
            (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue
                  (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
                  ((f.mem_sourceFiber_iff
                    (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).g
              (β (Real.smoothTransition t)) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  (β (Real.smoothTransition t)))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                  ℝ →L[ℝ] ℝ) (1 : ℝ)))) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrand om t)
      = SmoothPath.applyCotangent
          (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue
                  hβ0_reg
                  ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
              (β (Real.smoothTransition t)) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                (β (Real.smoothTransition t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  intro hβ0_reg
  -- Replace each summand with the per-fiber chain-expanded form.
  have h_each : ∀ p ∈ (f.sourceFiber hβ0_reg).attach,
      (f.sourceFiberPath hnc hβ_smooth hβ_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrand om t
        = SmoothPath.applyCotangent
            (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue
                  hβ0_reg
                  ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
              (β (Real.smoothTransition t)) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  (β (Real.smoothTransition t)))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                  ℝ →L[ℝ] ℝ) (1 : ℝ))) :=
    fun p _ => h_per_fiber p
  rw [Finset.sum_congr rfl h_each]
  -- Pull `applyCotangent` outside the finite sum.
  exact f.applyCotangent_sourceFiber_sum_cotangentPullbackAt hnc hβ_reg om 1

end MeromorphicNonzero

end JacobianChallenge

end
