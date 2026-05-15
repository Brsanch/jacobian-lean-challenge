/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathAmbientInjOn
import JacobianChallenge.Manifold.MeromorphicNonzeroTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Image of `sourceFiber` under `sourceFiberPath.toPath.extend t` lies in
`fiberFinset at β(σ t)`

For `t ∈ Icc 0 1`, every `x ∈ sourceFiber` maps to a point lying over
`β(σ t)` (i.e., in `fiberFinset (β(σ t))`). Combined with the
`InjOn`-form of the generalised injectivity
(`sourceFiberPath_toPath_extend_injOn_at`), this packages the map

```
sourceFiber.attach → fiberFinset (β(σ t))
  p ↦ (sourceFiberPath p).toPath.extend t
```

as a `Set.InjOn` with image ⊆ `fiberFinset`. Closing the bijection to
**onto** `fiberFinset (β(σ t))` requires either:

1. Generalising the heavy time-reversal argument
   (`sourceFiberPath_tgt_surjOn`) to arbitrary `t`, or
2. A cardinality argument: |sourceFiber| = |fiberFinset (β(σ t))| from
   the `degreeFiber` invariance, plus injectivity → bijection.

Either route is multi-hundred LOC of additional infrastructure. This
chip ships the **subset/injection** half of the bijection structurally;
the equality (surjectivity) remains a downstream named hypothesis or
classical input.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Each path's `toPath.extend t` lies over `β(σ t)` -/

/-- **`(sourceFiberPath x).toPath.extend t` lies over `β(σ t)`** for
`t ∈ Icc 0 1`. -/
lemma sourceFiberPath_toPath_extend_lifts_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t)
      = β (Real.smoothTransition t) := by
  rw [Path.extend_extends'
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨t, ht⟩]
  exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx ⟨t, ht⟩

/-! ## Image-in-fiberFinset membership -/

/-- **`(sourceFiberPath x).toPath.extend t ∈ fiberFinset (β(σ t))`.** -/
lemma sourceFiberPath_toPath_extend_mem_fiberFinset_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet) :
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t
      ∈ f.fiberFinset hβσt_reg := by
  rw [f.mem_fiberFinset_iff hβσt_reg]
  exact f.sourceFiberPath_toPath_extend_lifts_at hnc hβ_smooth hβ_reg hx ht

/-! ## `Set.InjOn` form of the generalised injectivity -/

/-- **`Set.InjOn` form of `sourceFiberPath_toPath_extend_injOn_at`.** The
map `p ↦ (sourceFiberPath p).toPath.extend t` (with `p ∈ sourceFiber`)
is `Set.InjOn` over `(sourceFiber).attach`. -/
theorem sourceFiberPath_toPath_extend_injOn_attach_at
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    Set.InjOn
      (fun p : (f.sourceFiber hβ0_reg) =>
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t)
      ((f.sourceFiber hβ0_reg).attach : Set _) := by
  intro hβ0_reg p₁ _ p₂ _ h_eq
  apply Subtype.ext
  exact f.sourceFiberPath_toPath_extend_injOn_at hnc hβ_smooth hβ_reg
    ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property)
    ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property)
    ht h_eq

/-! ## Finset image ⊆ fiberFinset -/

/-- **Finset image inclusion: `image of sourceFiber.attach ⊆ fiberFinset
(β(σ t))`.** -/
theorem sourceFiberPath_toPath_extend_image_subset_fiberFinset_at
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    (f.sourceFiber hβ0_reg).attach.image
        (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).toPath.extend t)
      ⊆ f.fiberFinset hβσt_reg := by
  intro hβ0_reg
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨p, _, rfl⟩ := hy
  exact f.sourceFiberPath_toPath_extend_mem_fiberFinset_at hnc hβ_smooth hβ_reg
    ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property) ht hβσt_reg

end MeromorphicNonzero

end JacobianChallenge

end
