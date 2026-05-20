/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.AbelJacobiPath

set_option linter.unusedSectionVars false

/-! # `complexChainPeriodVector` of the level-set chain as a Finset sum

The `levelSetChain f β` is defined as
`Σ_{p ∈ sourceFiber} SmoothChain.single (sourceFiberPath p)`. By
`complexChainPeriodVector`'s additivity (bundled in
`complexChainPeriodVectorHom`), its period vector decomposes as a
Finset sum over `sourceFiber.attach` of the per-path period vectors.

This is the period-vector analogue of
`MeromorphicNonzero.integrate_levelSetChain` (which gives the same
decomposition for `SmoothChain.integrate`). Useful for downstream
work on the period-in-lattice claim (the residual content of step 9
of the AbelGenerator arc).

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

/-- **Period vector of the level-set chain as a Finset sum.**

`complexChainPeriodVector α (levelSetChain f β)`
unfolds to `Σ_{p ∈ sourceFiber.attach}
  complexChainPeriodVector α (single (sourceFiberPath p))`. -/
theorem complexChainPeriodVector_levelSetChain_eq_sum
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    complexChainPeriodVector α (f.levelSetChain hnc hβ_smooth hβ_reg)
      = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          complexChainPeriodVector α
            (SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))) := by
  intro hβ0_reg
  -- Unfold levelSetChain to its Finset.sum form and apply the hom.
  show complexChainPeriodVector α
      (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
        SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)))
    = _
  rw [show complexChainPeriodVector α
        (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
            ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)))
      = complexChainPeriodVectorHom α
          (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            SmoothChain.single (f.sourceFiberPath hnc hβ_smooth hβ_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)))
      from rfl]
  rw [map_sum]
  rfl

end MeromorphicNonzero

end JacobianChallenge

end
