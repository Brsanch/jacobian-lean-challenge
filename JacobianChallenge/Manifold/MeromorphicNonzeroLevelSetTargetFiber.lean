/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetTargetSurjective
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChainBoundary

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Target-fiber identification: `Finset.image (·.tgt) sourceFiber = targetFiber`

For `β` smooth and regular on `Icc 0 1`, the target map `x ↦
(sourceFiberPath x).tgt` maps `sourceFiber` bijectively onto
`targetFiber := f.toRiemannSphere ⁻¹' {β 1}`. This follows from the
injectivity (7a) and surjectivity (7b) chips.

As a consequence, `targetFiberDivisor` rewrites as a Finset sum
over `targetFiber` directly (rather than indexed by `sourceFiber`).

This is **step 7c of the C3 staircase**: bridging the level-set chain's
boundary (target — source) to an explicit form indexed by the target
fiber. Step 7d will identify `targetFiber − sourceFiber` (as Finsupp)
with `−principalDivisorMap f` via order-1 matching at regular values.

## What ships

* `MeromorphicNonzero.targetFiber` — the target fiber as a `Finset X`.
* `MeromorphicNonzero.mem_targetFiber_iff`.
* `MeromorphicNonzero.sourceFiberPath_tgt_mem_targetFiber` — paths
  target into `targetFiber`.
* `MeromorphicNonzero.sourceFiberPath_tgt_image_eq_targetFiber` — the
  image equals the target fiber as Finsets.
* `MeromorphicNonzero.targetFiberDivisor_eq_sum_over_targetFiber` —
  re-indexing of the target divisor.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Target fiber** `f⁻¹({β 1})` as a `Finset`, given `β 1` regular. -/
noncomputable def targetFiber
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ1_reg : β 1 ∈ f.regularValueSet) :
    Finset X :=
  (f.fiber_finite_of_mem_regularValueSet hβ1_reg).toFinset

@[simp] lemma mem_targetFiber_iff
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ1_reg : β 1 ∈ f.regularValueSet)
    (y : X) :
    y ∈ f.targetFiber hβ1_reg ↔ f.toRiemannSphere y = β 1 := by
  unfold targetFiber
  rw [Set.Finite.mem_toFinset]
  rfl

/-- Each chosen path's target lies in the target fiber. -/
lemma sourceFiberPath_tgt_mem_targetFiber
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    let hβ1_reg : β 1 ∈ f.regularValueSet :=
      hβ_reg 1 ⟨by norm_num, le_refl _⟩
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).tgt ∈
      f.targetFiber hβ1_reg := by
  intro hβ1_reg
  rw [f.mem_targetFiber_iff hβ1_reg]
  exact f.sourceFiberPath_tgt_lift hnc hβ_smooth hβ_reg hx

/-- **Image of target map = target fiber as `Finsets`.** -/
theorem sourceFiberPath_tgt_image_eq_targetFiber
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    let hβ1_reg : β 1 ∈ f.regularValueSet :=
      hβ_reg 1 ⟨by norm_num, le_refl _⟩
    (f.sourceFiber hβ0_reg).attach.image
        (fun p => (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).tgt)
      = f.targetFiber hβ1_reg := by
  classical
  intro hβ0_reg hβ1_reg
  apply Finset.ext
  intro y
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, _, rfl⟩
    rw [f.mem_targetFiber_iff hβ1_reg]
    exact f.sourceFiberPath_tgt_lift hnc hβ_smooth hβ_reg _
  · intro hy
    -- y ∈ targetFiber. Surjectivity: ∃ x ∈ sourceFiber, (sourceFiberPath x).tgt = y.
    have hy_lift : f.toRiemannSphere y = β 1 :=
      (f.mem_targetFiber_iff hβ1_reg y).mp hy
    obtain ⟨x, hx_lift, h_tgt⟩ :=
      f.sourceFiberPath_tgt_surjOn hnc hβ_smooth hβ_reg hy_lift
    have hx_mem : x ∈ f.sourceFiber hβ0_reg :=
      (f.mem_sourceFiber_iff hβ0_reg x).mpr hx_lift
    refine ⟨⟨x, hx_mem⟩, Finset.mem_attach _ _, ?_⟩
    convert h_tgt using 2

/-- **Target divisor rewritten as a sum over the target fiber.** -/
theorem targetFiberDivisor_eq_sum_over_targetFiber
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    let hβ1_reg : β 1 ∈ f.regularValueSet :=
      hβ_reg 1 ⟨by norm_num, le_refl _⟩
    f.targetFiberDivisor hnc hβ_smooth hβ_reg
      = ∑ y ∈ f.targetFiber hβ1_reg, Finsupp.single y (1 : ℤ) := by
  classical
  intro hβ1_reg
  have hβ0_reg : β 0 ∈ f.regularValueSet :=
    hβ_reg 0 ⟨le_refl _, by norm_num⟩
  -- Unfold targetFiberDivisor.
  show ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
      Finsupp.single
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).tgt
        (1 : ℤ)
    = ∑ y ∈ f.targetFiber hβ1_reg, Finsupp.single y (1 : ℤ)
  -- Re-index via Finset.sum_image (target map is injective on attach by 7a).
  have h_image := f.sourceFiberPath_tgt_image_eq_targetFiber
    hnc hβ_smooth hβ_reg
  -- The map (fun p => tgt) is injective on attach.
  have h_inj :
      Set.InjOn
        (fun p : (f.sourceFiber hβ0_reg) =>
          (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).tgt)
        ((f.sourceFiber hβ0_reg).attach : Set _) := by
    intro p₁ _ p₂ _ h_eq
    apply Subtype.ext
    exact f.sourceFiberPath_tgt_injOn hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p₁.val).mp p₁.property)
      ((f.mem_sourceFiber_iff hβ0_reg p₂.val).mp p₂.property)
      h_eq
  -- Apply Finset.sum_image.
  rw [← h_image, Finset.sum_image h_inj]

/-- **Headline: boundary of level-set chain in fiber form.** -/
theorem boundary_levelSetChain_eq_fiberDiff
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    let hβ1_reg : β 1 ∈ f.regularValueSet :=
      hβ_reg 1 ⟨by norm_num, le_refl _⟩
    SmoothChain.boundary (f.levelSetChain hnc hβ_smooth hβ_reg)
      = (∑ y ∈ f.targetFiber hβ1_reg, Finsupp.single y (1 : ℤ))
        - (∑ x ∈ f.sourceFiber hβ0_reg, Finsupp.single x (1 : ℤ)) := by
  classical
  intro hβ0_reg hβ1_reg
  rw [f.boundary_levelSetChain hnc hβ_smooth hβ_reg]
  congr 1
  · exact f.targetFiberDivisor_eq_sum_over_targetFiber hnc hβ_smooth hβ_reg
  · -- sourceFiberDivisor = Σ x ∈ sourceFiber, Finsupp.single x 1.
    unfold sourceFiberDivisor
    rw [Finset.sum_attach (f.sourceFiber hβ0_reg)
        (fun x => Finsupp.single x (1 : ℤ))]

end MeromorphicNonzero

end JacobianChallenge

end
