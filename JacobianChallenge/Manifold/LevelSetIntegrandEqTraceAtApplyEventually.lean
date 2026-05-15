/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LevelSetIntegrandEqTraceAtApply
import JacobianChallenge.Manifold.PerFiberChainRuleEventually
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAtEventually

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Integrand-trace identity in full eventually form near `t = 0`

Composes:
* `eventually_forall_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply`
  (per-fibre chain rule eventually).
* `eventually_forall_betaSigma_in_sheetV` (sub-interval condition).
* `eventually_forall_sheet_lift_eq` (lift-equality).
* β(σ t) ∈ regularValueSet eventually.
* `sum_sourceFiber_integrand_eq_traceAt_apply` (per-`t` integrand-trace
  identity).

Headline:

```
∀ᶠ t in 𝓝[>] 0, ∃ hβσt_reg,
  ∑ p ∈ sourceFiber.attach, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σ t) σ'(t))
```

This is the integrand-level identity in fully eventually form near `0`,
integrating to the corresponding integral identity on a sub-interval
of `[0, 1]`. Lebesgue subdivision over Hurwitz patches lifts to global
`[0, 1]`.

## What ships

* `MeromorphicNonzero.eventually_sum_sourceFiber_integrand_eq_traceAt_apply`
  — the headline composition.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Integrand-trace identity in full eventually form near `0`.** -/
theorem eventually_sum_sourceFiber_integrand_eq_traceAt_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (hβ0_reg : β 0 ∈ f.regularValueSet) :
    ∀ᶠ t in 𝓝[Ioc (0 : ℝ) 1] (0 : ℝ),
      ∃ hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet,
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
  -- Eventually conditions in finer filters; transfer to 𝓝[Ioc 0 1] 0.
  -- 𝓝[Ioc 0 1] 0 ⊆ 𝓝[>] 0 (Ioc 0 1 ⊆ Ioi 0) — for the per-fibre chain rule eventually.
  -- 𝓝[Ioc 0 1] 0 ⊆ 𝓝[≥] 0 — for the lift-equality eventually.
  -- 𝓝[Ioc 0 1] 0 ⊆ 𝓝 0 — for the regularity / sub-interval eventually.
  have h_chain_ev :=
    f.eventually_forall_sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
      hnc hβ_smooth hβ_reg om
  have h_sub_ev := f.eventually_forall_betaSigma_in_sheetV hnc hβ_smooth hβ_reg
  have h_lift_ev := f.eventually_forall_sheet_lift_eq hnc hβ_smooth hβ_reg
  have h_reg_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      β (Real.smoothTransition t) ∈ f.regularValueSet := by
    have hβσ_cont : Continuous (fun t : ℝ => β (Real.smoothTransition t)) :=
      hβ_smooth.continuous.comp Real.smoothTransition.continuous
    have h0_in : (0 : ℝ) ∈ (fun t : ℝ => β (Real.smoothTransition t))
        ⁻¹' f.regularValueSet := by
      simp only [Set.mem_preimage, Real.smoothTransition.zero]; exact hβ0_reg
    exact (hβσ_cont.isOpen_preimage _ (f.regularValueSet_isOpen hnc)).mem_nhds h0_in
  -- Transfer to 𝓝[Ioc 0 1] 0.
  have h_Ioc_le_pos : 𝓝[Ioc (0:ℝ) 1] (0 : ℝ) ≤ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_mono _ Ioc_subset_Ioi_self
  have h_Ioc_le_Ici : 𝓝[Ioc (0:ℝ) 1] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) :=
    nhdsWithin_mono _ (fun _ ⟨h1, _⟩ => le_of_lt h1)
  have h_Ioc_le_nhds : 𝓝[Ioc (0:ℝ) 1] (0 : ℝ) ≤ 𝓝 (0 : ℝ) :=
    nhdsWithin_le_nhds
  have h_chain_Ioc := h_Ioc_le_pos h_chain_ev
  have h_sub_Ioc := h_Ioc_le_nhds h_sub_ev
  have h_lift_Ioc := h_Ioc_le_Ici h_lift_ev
  have h_reg_Ioc := h_Ioc_le_nhds h_reg_ev
  have h_self_Ioc : ∀ᶠ t in 𝓝[Ioc (0:ℝ) 1] (0 : ℝ),
      t ∈ Icc (0 : ℝ) 1 := by
    have h_Ioc_in : ∀ᶠ t in 𝓝[Ioc (0:ℝ) 1] (0 : ℝ), t ∈ Ioc (0:ℝ) 1 :=
      self_mem_nhdsWithin
    filter_upwards [h_Ioc_in] with t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  filter_upwards [h_chain_Ioc, h_sub_Ioc, h_lift_Ioc, h_reg_Ioc, h_self_Ioc] with
    t h_chain_t h_sub_t h_lift_t h_reg_t h_self_t
  refine ⟨h_reg_t, ?_⟩
  -- Apply the per-`t` chip.
  exact f.sum_sourceFiber_integrand_eq_traceAt_apply hnc hβ_smooth hβ_reg om
    h_self_t h_reg_t hβ0_reg h_chain_t h_sub_t h_lift_t

end MeromorphicNonzero

end JacobianChallenge

end
