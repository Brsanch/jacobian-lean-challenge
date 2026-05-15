/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftSmoothPath
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Level-set chain on a smooth regular path β

For a non-constant `f : MeromorphicNonzero X` and a `C^∞` path
`β : ℝ → RiemannSphere` taking regular values on `Icc 0 1`, the
**level-set chain** is the sum (over the source fiber `f⁻¹({β 0})`)
of the smooth lifts of `β` starting at each fiber point.

The fiber over the regular value `β 0` is finite (chip 9,
`fiber_finite_of_mem_regularValueSet`). For each fiber point `x`,
chip step 4 (`exists_smoothPath_of_lift_on_unitInterval`) supplies a
`SmoothPath 𝓘(ℝ, ℂ) X` with source `x` and target a preimage of
`β 1`. The level-set chain is the formal `ℤ`-sum of the resulting
singleton chains with coefficient `+1` at each fiber point.

This is **step 5 of the 9-step C3 general-genus arc**. Subsequent
steps will compute the boundary of this chain (step 6), identify it
with `principalDivisorMap f` when `β : 0 → ∞` (step 7), and discharge
the period-lattice content via Stokes on a 2-chain (steps 8–9).

## What ships

* `MeromorphicNonzero.sourceFiber` — the source fiber as a `Finset X`.
* `MeromorphicNonzero.sourceFiberPath` — for each fiber point, a
  classically-chosen `SmoothPath` lifting `β`.
* `MeromorphicNonzero.levelSetChain` — the formal sum
  `Σ_{x ∈ sourceFiber} single (sourceFiberPath x)` as a
  `SmoothChain 𝓘(ℝ, ℂ) X`.
* `MeromorphicNonzero.sourceFiberPath_src` /
  `MeromorphicNonzero.sourceFiberPath_tgt_lift` — characterising
  properties of the chosen paths.

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

/-- **Source fiber** `f⁻¹({β 0})` as a `Finset`. Requires `β 0` to be a
regular value (then chip 9 provides finiteness). -/
noncomputable def sourceFiber
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ0_reg : β 0 ∈ f.regularValueSet) :
    Finset X :=
  (f.fiber_finite_of_mem_regularValueSet hβ0_reg).toFinset

@[simp] lemma mem_sourceFiber_iff
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ0_reg : β 0 ∈ f.regularValueSet)
    (x : X) :
    x ∈ f.sourceFiber hβ0_reg ↔ f.toRiemannSphere x = β 0 := by
  unfold sourceFiber
  rw [Set.Finite.mem_toFinset]
  rfl

/-- **Path from a source-fiber point.** Classical choice of a smooth lift
of `β` starting at `x ∈ sourceFiber f hβ0_reg`. -/
noncomputable def sourceFiberPath
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    SmoothPath 𝓘(ℝ, ℂ) X :=
  (f.exists_smoothPath_of_lift_on_unitInterval hnc hβ_smooth x hβ_reg hx).choose

/-- The chosen path's source is the requested fiber point. -/
lemma sourceFiberPath_src
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).src = x :=
  (f.exists_smoothPath_of_lift_on_unitInterval
    hnc hβ_smooth x hβ_reg hx).choose_spec.1

/-- The chosen path's target lies over `β 1`. -/
lemma sourceFiberPath_tgt_lift
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    f.toRiemannSphere (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).tgt = β 1 :=
  (f.exists_smoothPath_of_lift_on_unitInterval
    hnc hβ_smooth x hβ_reg hx).choose_spec.2

/-- **Level-set chain on `β`.** The formal sum
`Σ_{x ∈ sourceFiber} single (sourceFiberPath x)` as a
`SmoothChain 𝓘(ℝ, ℂ) X`. -/
noncomputable def levelSetChain
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    SmoothChain 𝓘(ℝ, ℂ) X := by
  classical
  have hβ0_reg : β 0 ∈ f.regularValueSet :=
    hβ_reg 0 ⟨le_refl _, by norm_num⟩
  exact ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
    SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))

/-- **Level-set chain unfolds to the explicit Finset sum** over
`sourceFiber.attach`. -/
lemma levelSetChain_eq
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    f.levelSetChain hnc hβ_smooth hβ_reg
      = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)) := by
  rfl

end MeromorphicNonzero

end JacobianChallenge

end
