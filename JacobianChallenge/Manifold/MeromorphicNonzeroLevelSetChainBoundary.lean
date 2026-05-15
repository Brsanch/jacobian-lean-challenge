/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Boundary of the level-set chain

The chain `levelSetChain f β` is a sum over the source fiber of
singleton smooth-chain components. Its boundary under
`SmoothChain.boundary` is therefore the corresponding sum of
`boundarySingle`s, each of which is `δ_{tgt} - δ_{src}`. Combining:

  `∂(levelSetChain f β) = (Σ_{x ∈ sourceFiber} δ_{tgt(path x)})
                          − (Σ_{x ∈ sourceFiber} δ_x)`.

The second sum is the **source divisor** (sum of `δ_x` for `x` in
the fiber over `β 0`). The first sum is the **target divisor**: the
multiset of targets of the chosen smooth lifts, viewed as a `Finsupp`.

This is **step 6 of the 9-step C3 general-genus arc**. Step 7 will
identify this with `principalDivisorMap f` under the choice `β : 0 → ∞`.

## What ships

* `MeromorphicNonzero.sourceFiberDivisor` — the source divisor as a
  `X →₀ ℤ`.
* `MeromorphicNonzero.targetFiberDivisor` — the target divisor.
* `MeromorphicNonzero.boundary_levelSetChain` — the headline identity
  `∂(levelSetChain) = targetFiberDivisor − sourceFiberDivisor`.

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

/-- **Source divisor.** Sum of `δ_x` over the source fiber as a
`Finsupp`. -/
noncomputable def sourceFiberDivisor
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ0_reg : β 0 ∈ f.regularValueSet) :
    X →₀ ℤ :=
  ∑ p ∈ (f.sourceFiber hβ0_reg).attach, Finsupp.single p.val 1

/-- **Target divisor.** Sum of `δ_{(sourceFiberPath x).tgt}` over the
source fiber as a `Finsupp`. -/
noncomputable def targetFiberDivisor
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    X →₀ ℤ := by
  classical
  have hβ0_reg : β 0 ∈ f.regularValueSet :=
    hβ_reg 0 ⟨le_refl _, by norm_num⟩
  exact ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
    Finsupp.single
      (f.sourceFiberPath hnc hβ_smooth hβ_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).tgt
      (1 : ℤ)

/-- **Headline boundary identity.** The boundary of the level-set
chain equals the target divisor minus the source divisor. -/
theorem boundary_levelSetChain
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    SmoothChain.boundary (f.levelSetChain hnc hβ_smooth hβ_reg)
      = f.targetFiberDivisor hnc hβ_smooth hβ_reg
        - f.sourceFiberDivisor hβ0_reg := by
  classical
  -- Unfold levelSetChain to the Finset.sum form.
  simp only [levelSetChain, map_sum, SmoothChain.boundary_single,
    SmoothChain.boundarySingle]
  -- The sum decomposes as (Σ tgt-terms) - (Σ src-terms).
  rw [Finset.sum_sub_distrib]
  congr 1
  -- Each `Finsupp.single` summand matches definitionally.
  -- The src-side uses `sourceFiberPath_src` (the source equals the chosen point).
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [f.sourceFiberPath_src hnc hβ_smooth hβ_reg
    ((f.mem_sourceFiber_iff _ p.val).mp p.property)]

end MeromorphicNonzero

end JacobianChallenge

end
