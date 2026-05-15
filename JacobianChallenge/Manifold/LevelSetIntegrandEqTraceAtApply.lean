/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LevelSetIntegralChainRuleStructural
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Integrand-level identity: source-side chain-rule sum = trace-applyCotangent

Composes the chain-rule structural identity
(`sum_sourceFiber_integrand_chain_at`) with the per-`t` trace identity
(`source_sheet_sum_eq_traceAt`) to obtain:

```
∑_{p ∈ sourceFiber} (sourceFiberPath p).integrand om t
  = applyCotangent (traceAt(f)(β(σ t))(om)) (β'(σt) σ'(t))
```

at any `t` where the per-fiber chain-rule hypothesis (sheet-`g`
realified smoothness at `β(σ t)`), the sub-interval condition
(`β(σ t) ∈ sheet_p.V` per p), and the lift-equality
(`(sourceFiberPath p).toPath.extend t = sheet_p.g (β(σ t))` per p)
all hold.

This is the **integrand of `(levelSetChain f β).integrate om`** equating
to the **integrand of the line integral of `f_*ω` along β** (after
σ-reparametrisation). It bridges the source-side chain integral to the
target-side trace 1-form integral on a per-`t` basis.

The integrated identity (composing across `[0, 1]` via Lebesgue
subdivision over Hurwitz patches) is the next layer.

## What ships

* `MeromorphicNonzero.sum_sourceFiber_integrand_eq_traceAt_apply` —
  the integrand-level per-`t` identity.

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

/-- **Integrand-level per-`t` identity.** Source-side chain-rule sum
collapses to the trace-applyCotangent at `β(σ t)`. -/
theorem sum_sourceFiber_integrand_eq_traceAt_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet)
    (hβ0_reg : β 0 ∈ f.regularValueSet)
    (h_per_fiber : ∀ p : { x : X // x ∈ f.sourceFiber hβ0_reg },
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
                  ℝ →L[ℝ] ℝ) (1 : ℝ))))
    (h_sub_interval :
      ∀ p : { x : X // x ∈ f.sourceFiber hβ0_reg },
        β (Real.smoothTransition t) ∈
          (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue hβ0_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).V)
    (h_lift_eq :
      ∀ p : { x : X // x ∈ f.sourceFiber hβ0_reg },
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t
          = (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue hβ0_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
              (β (Real.smoothTransition t))) :
    ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrand om t
      = SmoothPath.applyCotangent
          (f.traceAt hnc hβσt_reg om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                (β (Real.smoothTransition t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  classical
  -- Stage 1: chain-rule structural identity reduces the integrand sum to
  -- applyCotangent of the source-side cotangent pullback sum.
  have h_chain :=
    f.sum_sourceFiber_integrand_chain_at hnc hβ_smooth hβ_reg om
      (t := t) h_per_fiber
  -- Stage 2: trace identity converts the source-side cotangent pullback sum
  -- to traceAt at β(σ t). We need to massage the form: the chain-rule's
  -- output uses bare `cotangentPullbackAt`, while source_sheet_sum_eq_traceAt
  -- uses `sheetCotPullback`. They unfold to the same thing.
  have h_trace :=
    f.source_sheet_sum_eq_traceAt hnc hβ_smooth hβ_reg om ht hβσt_reg hβ0_reg
      h_sub_interval h_lift_eq
  -- The trace identity is stated in `sheetCotPullback` form, which unfolds
  -- to `cotangentPullbackAt` definitionally.
  rw [h_chain]
  -- Goal: applyCotangent (∑ ..., cotPullback over β 0 sheets at β(σ t)) m
  --     = applyCotangent (traceAt f hnc hβσt_reg om at β(σ t)) m
  -- The two arguments differ; bridge via the trace identity h_trace.
  -- h_trace says: ∑ p ∈ sourceFiber, sheetCotPullback ... = traceAt(...)
  -- which unfolds to: ∑ ..., cotPullback (sheet over β 0 at β(σ t)) = traceAt(...)
  rw [show (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
          (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue hβ0_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))).g
          (β (Real.smoothTransition t)) om)
      = f.traceAt hnc hβσt_reg om from h_trace]

end MeromorphicNonzero

end JacobianChallenge

end
