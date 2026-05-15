/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandChainAtT
import JacobianChallenge.Manifold.SourceFiberPathAmbientSurjOnAt
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.MeromorphicNonzeroTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Global integrand-trace identity at any regular `t ∈ Ioo 0 1`

For any `t ∈ Ioo 0 1` (strictly interior), the per-fibre lifted-point
chain-rule identity at `t₀ = t` gives, for each `p ∈ sourceFiber(β 0)`:

```
(sourceFiberPath p).integrand om t
  = applyCotangent (cotangentPullbackAt sheet_{extend t p}.g (β(σ t)) om)
      (mfderiv β (σ t) (mfderiv σ t 1))
```

Summing over `p` and re-indexing via the bijection `p ↔ extend t p`
(sourceFiber → fiberFinset(β(σ t))) gives the **global** integrand-
trace identity:

```
∑ p ∈ sourceFiber, (sourceFiberPath p).integrand om t
  = applyCotangent (traceAt f hnc hβσt_reg om) (mfderiv β (σ t) (mfderiv σ t 1))
```

at every `t ∈ Ioo 0 1` — no sub-interval restriction, no Lebesgue
subdivision required. Boundary cases `t = 0, 1` are Lebesgue-null
and irrelevant for integration.

## What ships

* `MeromorphicNonzero.global_integrand_eq_traceAt_apply` — the
  headline global per-`t` integrand identity at `t ∈ Ioo 0 1`.

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

/-- Auxiliary: at `t ∈ Ioo 0 1`, the per-fibre lifted-point chain-rule
identity holds at `u = t` itself (using the strict open-interval
membership exposed by the chip). -/
private lemma per_fiber_chain_at_interior_t
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let γ := (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend
    let q := γ t
    let hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet :=
      hβ_reg (Real.smoothTransition t)
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    let hq_lift : f.toRiemannSphere q = β (Real.smoothTransition t) := by
      have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t)
        = β (Real.smoothTransition t)
      rw [Path.extend_extends'
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨t, ht_Icc⟩]
      exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx ⟨t, ht_Icc⟩
    let hq_reg : q ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hβσt_reg hq_lift
    let sheet_q := f.localSheetData_at_regular hnc hq_reg
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).integrand om t
      = SmoothPath.applyCotangent
          (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            sheet_q.g (β (Real.smoothTransition t)) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                (β (Real.smoothTransition t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  intros γ q hβσt_reg hq_lift hq_reg sheet_q
  have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  obtain ⟨a, b, _ha_mem, _hb_mem, _ha_le_t, _ht_le_b, ha_lt_t, ht_lt_b, h_id⟩ :=
    f.sourceFiberPath_integrand_chain_at_lifted_sheet hnc hβ_smooth hβ_reg hx
      om ht_Icc
  exact h_id t ⟨ha_lt_t ht.1, ht_lt_b ht.2⟩

/-- **Global per-`t` integrand-trace identity at `t ∈ Ioo 0 1`.**

The source-side integrand sum equals `applyCotangent` of `traceAt`
times the velocity, with no sub-interval restriction.

The proof: per fibre, the lifted-point chain-rule chip gives the
identity in terms of `sheet_{extend t p}.g`. Summing and re-indexing
via the bijection `p ↔ extend t p` (which IS sourceFiber ↔
fiberFinset(β(σ t))) gives `traceAt(f)(β(σ t))(om)` directly — each
summand is a trace summand at the lifted point. -/
theorem global_integrand_eq_traceAt_apply
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ s ∈ Icc (0 : ℝ) 1, β s ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (hβ0_reg : β 0 ∈ f.regularValueSet)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet :=
      hβ_reg (Real.smoothTransition t)
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
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
  intro hβσt_reg
  -- Step 1: per-p, chain-rule identity at u = t.
  have h_per_p :
      ∀ p ∈ (f.sourceFiber hβ0_reg).attach,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrand om t
        = SmoothPath.applyCotangent
            (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue hβσt_reg
                  (by
                    have ht_Icc : t ∈ Icc (0 : ℝ) 1 :=
                      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
                    show f.toRiemannSphere
                      ((f.sourceFiberPath hnc hβ_smooth hβ_reg
                        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp
                          p.property)).toPath.extend t)
                      = β (Real.smoothTransition t)
                    rw [Path.extend_extends'
                      (f.sourceFiberPath hnc hβ_smooth hβ_reg
                        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp
                          p.property)).toPath ⟨t, ht_Icc⟩]
                    exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg
                      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)
                      ⟨t, ht_Icc⟩))).g
              (β (Real.smoothTransition t)) om)
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition t) :
                ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                  (β (Real.smoothTransition t)))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition t :
                  ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
    intro p _
    exact per_fiber_chain_at_interior_t f hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property) om ht
  -- Step 2: rewrite each summand.
  rw [Finset.sum_congr rfl h_per_p]
  -- Step 3: applyCotangent traceAt = ∑ q ∈ fiberFinset, applyCotangent (cotPullback sheet_q.g …)
  rw [f.applyCotangent_traceAt hnc hβσt_reg om]
  -- Step 4: re-index via the bijection p ↦ extend t p.
  -- The map: p ∈ sourceFiber.attach → ⟨extend t p, in fiberFinset⟩.
  refine Finset.sum_bij
    (fun p _ =>
      ⟨(f.sourceFiberPath hnc hβ_smooth hβ_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t,
      by
        rw [f.mem_fiberFinset_iff hβσt_reg]
        have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        show f.toRiemannSphere
          ((f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t)
          = β (Real.smoothTransition t)
        rw [Path.extend_extends'
          (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath ⟨t, ht_Icc⟩]
        exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property) ⟨t, ht_Icc⟩⟩) ?_ ?_ ?_ ?_
  · -- maps into target Finset.attach
    intro p _; exact Finset.mem_attach _ _
  · -- injectivity
    intro p₁ _ p₂ _ h_eq
    apply Subtype.ext
    have h_extend_eq :
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property)).toPath.extend t
          = (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property)).toPath.extend t :=
      Subtype.ext_iff.mp h_eq
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact f.sourceFiberPath_toPath_extend_injOn_at hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property)
      ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property)
      ht_Icc h_extend_eq
  · -- surjectivity
    intro q _
    have hq_finset : q.val ∈ f.fiberFinset hβσt_reg := q.property
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_image_eq :=
      f.sourceFiberPath_toPath_extend_image_eq_fiberFinset_at hnc hβ_smooth hβ_reg
        ht_Icc hβσt_reg
    have hq_in_image : q.val ∈ (f.sourceFiber hβ0_reg).attach.image
        (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t) := by
      rw [h_image_eq]; exact hq_finset
    rw [Finset.mem_image] at hq_in_image
    obtain ⟨p, hp_attach, h_extend_eq⟩ := hq_in_image
    exact ⟨p, hp_attach, Subtype.ext h_extend_eq⟩
  · -- summand congruence: same shape on both sides
    intro p _
    rfl

end MeromorphicNonzero

end JacobianChallenge

end
