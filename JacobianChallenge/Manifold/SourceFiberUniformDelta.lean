/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandPullback

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Uniform `δ` across `sourceFiber` for the per-fiber-point integrand chip

`sourceFiberPath_integrand_eq_cotangentPullbackAt_apply` produces a
per-fiber-point `δ_x ∈ (0, 1]`. This chip extracts a **uniform**
`δ ∈ (0, 1]` valid for every `x ∈ sourceFiber` simultaneously, by
taking `Finset.min'` over the finite sourceFiber.

The minimum is well-defined because:
* `sourceFiber f hβ0_reg` is a finite set (from
  `fiber_finite_of_mem_regularValueSet`).
* Each per-fiber chip's `δ_x > 0`.
* If `sourceFiber` is empty, the conclusion is vacuous; we take
  `δ := 1`.

This packaging lets downstream chips assert a single `δ` that
simultaneously satisfies every per-fiber chip's hypothesis.

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

/-! ## Per-fiber-point δ as a function -/

/-- **Per-fiber-point `δ_x` extracted via `Classical.choose`.** -/
noncomputable def perFiberDelta
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ℝ :=
  (f.sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    hnc hβ_smooth hβ_reg hx om).choose

/-- **`perFiberDelta` is positive.** -/
lemma perFiberDelta_pos
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    0 < f.perFiberDelta hnc hβ_smooth hβ_reg om hx :=
  (f.sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    hnc hβ_smooth hβ_reg hx om).choose_spec.1

/-- **`perFiberDelta ≤ 1`.** -/
lemma perFiberDelta_le_one
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    f.perFiberDelta hnc hβ_smooth hβ_reg om hx ≤ 1 :=
  (f.sourceFiberPath_integrand_eq_cotangentPullbackAt_apply
    hnc hβ_smooth hβ_reg hx om).choose_spec.2.1

/-! ## Uniform `δ` over `sourceFiber` -/

/-- **Uniform `δ` over `sourceFiber.attach`.** Defined as `Finset.min'`
of `perFiberDelta` when `sourceFiber` is non-empty; falls back to `1`
otherwise. -/
noncomputable def uniformFiberDelta
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    ℝ := by
  classical
  by_cases h_nonempty :
      (f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.Nonempty
  · exact (f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.image
      (fun p => f.perFiberDelta hnc hβ_smooth hβ_reg om
        ((f.mem_sourceFiber_iff
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))
      |>.min' (h_nonempty.image _)
  · exact 1

/-- **`uniformFiberDelta` is positive.** -/
theorem uniformFiberDelta_pos
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    0 < f.uniformFiberDelta hnc hβ_smooth hβ_reg om := by
  classical
  unfold uniformFiberDelta
  by_cases h_nonempty :
      (f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.Nonempty
  · rw [dif_pos h_nonempty]
    -- min' > 0 because every element in the image is positive (perFiberDelta_pos).
    have h_min_mem := Finset.min'_mem
      ((f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.image
        (fun q => f.perFiberDelta hnc hβ_smooth hβ_reg om
          ((f.mem_sourceFiber_iff
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) q.val).mp q.property)))
      (h_nonempty.image _)
    rw [Finset.mem_image] at h_min_mem
    obtain ⟨q, _, hq_eq⟩ := h_min_mem
    rw [← hq_eq]
    exact f.perFiberDelta_pos hnc hβ_smooth hβ_reg om _
  · rw [dif_neg h_nonempty]; exact one_pos

/-- **`uniformFiberDelta ≤ 1`.** -/
theorem uniformFiberDelta_le_one
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    f.uniformFiberDelta hnc hβ_smooth hβ_reg om ≤ 1 := by
  classical
  unfold uniformFiberDelta
  by_cases h_nonempty :
      (f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.Nonempty
  · rw [dif_pos h_nonempty]
    obtain ⟨p, hp⟩ := h_nonempty
    have hxp : f.toRiemannSphere p.val = β 0 :=
      (f.mem_sourceFiber_iff
        (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property
    have h_val_le : f.perFiberDelta hnc hβ_smooth hβ_reg om hxp ≤ 1 :=
      f.perFiberDelta_le_one hnc hβ_smooth hβ_reg om hxp
    have h_mem : f.perFiberDelta hnc hβ_smooth hβ_reg om hxp
        ∈ (f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.image
            (fun q => f.perFiberDelta hnc hβ_smooth hβ_reg om
              ((f.mem_sourceFiber_iff
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) q.val).mp q.property)) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    exact le_trans (Finset.min'_le _ _ h_mem) h_val_le
  · rw [dif_neg h_nonempty]

/-- **`uniformFiberDelta ≤ perFiberDelta p` for every `p ∈ sourceFiber`.**
This is the bound needed for `t ∈ Ioo 0 (uniformFiberDelta)` to imply
`t ∈ Ioo 0 (perFiberDelta p)` for every `p`. -/
theorem uniformFiberDelta_le_perFiberDelta
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (p : { x : X // x ∈ f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩) }) :
    f.uniformFiberDelta hnc hβ_smooth hβ_reg om
      ≤ f.perFiberDelta hnc hβ_smooth hβ_reg om
        ((f.mem_sourceFiber_iff
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property) := by
  classical
  unfold uniformFiberDelta
  have h_nonempty :
      (f.sourceFiber (hβ_reg 0 ⟨le_refl _, by norm_num⟩)).attach.Nonempty :=
    ⟨p, Finset.mem_attach _ _⟩
  rw [dif_pos h_nonempty]
  apply Finset.min'_le
  refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
  exact Finset.mem_attach _ _

end MeromorphicNonzero

end JacobianChallenge

end
