/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LevelSetChainPeriodVectorSum
import JacobianChallenge.Manifold.ComplexChainPeriodSingle

set_option linter.unusedSectionVars false

/-! # Explicit real+imag decomposition of the level-set chain period vector

Compose the Finset-sum decomposition
`complexChainPeriodVector_levelSetChain_eq_sum` (in tree) with the
single-path identity `complexChainPeriod_single` (in tree) to express
the `j`-th coordinate of the period vector as

```
complexChainPeriodVector α (levelSetChain f β) j
  = (Σ_p (sourceFiberPath p).integrate (realComponent (α j)) : ℝ : ℂ)
    + Complex.I *
        (Σ_p (sourceFiberPath p).integrate (imagComponent (α j)) : ℝ : ℂ)
```

This reduces the per-`f` period-in-lattice claim to **two real
Finset sums** (the real and imaginary parts of each per-path
integral, summed over the source fiber). The chain-rule pathway
(in-tree partially scaffolded via `SmoothPath.integrate_compSmoothPath`
+ `MeromorphicNonzeroSourceFiberPathSheetEq`) then connects each
per-path real integral to a `β`-line integral against the trace
form `traceAt α f`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Module
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Explicit real+imag decomposition of the `j`-th period vector
component of the level-set chain.**

The `j`-th coordinate of `complexChainPeriodVector α (levelSetChain f β)`
expands as a sum of complex-valued single-path periods, each of which
expands as `realIntegral + I * imagIntegral` (over `realComponent (α j)`
and `imagComponent (α j)` respectively). -/
theorem complexChainPeriodVector_levelSetChain_apply_eq_sum_real_imag
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (j : Fin (JacobianChallenge.genus X)) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    complexChainPeriodVector α (f.levelSetChain hnc hβ_smooth hβ_reg) j
      = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          ((((f.sourceFiberPath hnc hβ_smooth hβ_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
              (realComponent (α j)) : ℝ) : ℂ)
          + Complex.I *
              (((f.sourceFiberPath hnc hβ_smooth hβ_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                (imagComponent (α j)) : ℝ) : ℂ)) := by
  intro hβ0_reg
  -- Apply the period-vector sum decomposition, then evaluate at j.
  rw [complexChainPeriodVector_levelSetChain_eq_sum f hnc hβ_smooth hβ_reg α]
  -- The sum is evaluated at j; pull the j-application inside.
  rw [show ((∑ p ∈ (f.sourceFiber hβ0_reg).attach,
              complexChainPeriodVector α
                (SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
                  ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))))
            : Fin (JacobianChallenge.genus X) → ℂ) j
        = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            complexChainPeriodVector α
              (SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))) j from
      Finset.sum_apply _ _ _]
  -- Per-summand: rewrite via complexChainPeriod_single (showing this requires
  -- unfolding complexChainPeriodVector ... j to complexChainPeriod ... (α j)).
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show complexChainPeriod
      (SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
        ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))) (α j)
    = _
  exact complexChainPeriod_single _ _

end MeromorphicNonzero

end JacobianChallenge

end
