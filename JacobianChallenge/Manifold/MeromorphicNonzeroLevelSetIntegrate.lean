/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.SmoothChainIntegralLinearity

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Integral of a 1-form along the level-set chain

By `SmoothChain.integrate`-linearity (`integrateLinearMap` is a
ℤ-linear map), the integral of any 1-form `ω` against `levelSetChain
f β` decomposes as a sum over the source fiber:

  `(levelSetChain f β).integrate ω = Σ_{x ∈ sourceFiber} (sourceFiberPath x).integrate ω`.

This is **step 8 (bookkeeping) of the C3 staircase**: the natural
linearity unfolding. The substantive content of step 8 proper —
identifying the per-path integral with a pushforward-1-form integral
over β on `RiemannSphere` — uses the existing
`SmoothPath.integrate_compSmoothPath` chain-rule (from the c1 work)
applied path-by-path. That extension can be layered on top of this
linearity result.

## What ships

* `MeromorphicNonzero.integrate_levelSetChain` — the Finset-sum
  expansion of the level-set chain integral.

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

/-- **Integral of `ω` against the level-set chain.**

By linearity of `SmoothChain.integrate`, the integral expands as a
Finset sum over the source fiber of the per-path integrals. -/
theorem integrate_levelSetChain
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (oneForm : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    SmoothChain.integrate (f.levelSetChain hnc hβ_smooth hβ_reg) oneForm
      = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
            oneForm := by
  intro hβ0_reg
  -- Unfold levelSetChain to the Finset.sum and apply integrate-of-sum.
  show SmoothChain.integrate
      (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)))
      oneForm
    = _
  -- Use the linear-map form: integrateLinearMap oneForm is a ℤ-linear map.
  rw [show SmoothChain.integrate
        (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)))
        oneForm
      = SmoothChain.integrateLinearMap oneForm
        (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)))
      from rfl]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  exact SmoothChain.integrateLinearMap_single oneForm
    (f.sourceFiberPath hnc hβ_smooth hβ_reg
      ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))

end MeromorphicNonzero

end JacobianChallenge

end
