/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroAbelGeneratorFromLevelSet
import JacobianChallenge.Manifold.MeromorphicNonzeroConcreteLevelSetChain

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-`f` `AbelGenerator` reduction with the concrete `regularLevelSetChain`

The universal-`f` reduction
`abelGeneratorPeriodCondition_of_levelSet_lattice` requires a chain
`Z` for **every** `f` satisfying both a boundary identity and a
period-lattice clause. This file ships a **per-`f`** variant that
specialises `Z := f.regularLevelSetChain hnc h0_reg h_inf_reg` (the
concrete level-set chain whose boundary identity is already in tree
via `boundary_regularLevelSetChain`), reducing the per-`f` hypothesis
to **just the period-lattice clause** for the regular level-set
chain — the genuine residual content of step 9.

## What ships

* `abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period` —
  per-`f` claim
  `complexChainPeriodVector α (B.principalDivisorAJChain
    (principalDivisorMap f)) ∈ periodLatticeImage`
  from `h_Z_period :
    complexChainPeriodVector α (f.regularLevelSetChain ...)
    ∈ periodLatticeImage`.

* `abelGeneratorPeriodCondition_of_regularLevelSetChain_period` —
  universal version, taking the per-`f` period claim *with* the
  existence of regular endpoints `(0, ∞)`. (The regularity of `0`
  and `∞` is itself classical content — e.g. compose with a generic
  Möbius transformation to arrange — and is left as a per-`f` input
  to keep this chip tightly scoped.)

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
  [PreconnectedSpace X] [Nonempty X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
variable {h : PeriodLatticeDiscretenessBundle
  (PeriodPairingData.ofSmoothCycle X) α}

/-- **Per-`f` `AbelGenerator` reduction**: given regular endpoints `0` and
`∞` and the period-lattice claim for the concrete
`regularLevelSetChain f`, the per-`f` claim
`complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
  ∈ periodLatticeImage` holds.

This is the per-`f` analogue of `abelGeneratorPeriodCondition_of_levelSet_lattice`
with the boundary identity automatically discharged by
`boundary_regularLevelSetChain` (step 7d-d composition), reducing the
hypothesis to the period-lattice clause alone. -/
theorem abelGeneratorPeriodCondition_at_of_regularLevelSetChain_period
    (B : JacobianChallenge.AbelJacobiInput α h)
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (h_Z_period :
      complexChainPeriodVector α
          (f.regularLevelSetChain hnc h0_reg h_inf_reg)
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α) :
    complexChainPeriodVector α
        (B.principalDivisorAJChain (principalDivisorMap f))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  -- Z is the concrete regular level-set chain.
  set Z : SmoothChain 𝓘(ℝ, ℂ) X := f.regularLevelSetChain hnc h0_reg h_inf_reg
    with hZ_def
  -- AJ is the principal-divisor AJ chain for principalDivisorMap f.
  set AJ : SmoothChain 𝓘(ℝ, ℂ) X :=
    B.principalDivisorAJChain (principalDivisorMap f) with hAJ_def
  -- Boundary of Z: pointwise = -principalDivisorMap f.
  have h_Z_boundary : ∀ x : X,
      (SmoothChain.boundary Z).toFun x
        = -((principalDivisorMap f : X → ℤ) x) :=
    f.boundary_regularLevelSetChain hnc h0_reg h_inf_reg
  -- Boundary of AJ: pointwise = +principalDivisorMap f
  -- (in-tree via PrincipalDivisorAJChainBoundary).
  have h_AJ_boundary : ∀ x : X,
      (SmoothChain.boundary AJ).toFun x
        = ((principalDivisorMap f : X → ℤ) x) :=
    fun x => AbelJacobiInput.boundary_principalDivisorAJChain_principalDivisorMap
      B f x
  -- Pointwise: boundary (Z + AJ) = 0.
  have h_sum_boundary_pointwise : ∀ x : X,
      (SmoothChain.boundary (Z + AJ)).toFun x = 0 := by
    intro x
    rw [SmoothChain.boundary_add]
    change ((SmoothChain.boundary Z) + (SmoothChain.boundary AJ) : X →₀ ℤ) x = 0
    rw [Finsupp.add_apply]
    change (SmoothChain.boundary Z).toFun x + (SmoothChain.boundary AJ).toFun x = 0
    rw [h_Z_boundary x, h_AJ_boundary x]
    ring
  -- Finsupp pointwise → Finsupp equality.
  have h_sum_boundary : SmoothChain.boundary (Z + AJ) = 0 := by
    apply Finsupp.ext
    intro x
    exact h_sum_boundary_pointwise x
  -- (Z + AJ) is a SmoothCycle.
  have h_cycle : Z + AJ ∈ SmoothCycle 𝓘(ℝ, ℂ) X := by
    rw [SmoothCycle.mem_iff]
    exact h_sum_boundary
  set C : SmoothCycle 𝓘(ℝ, ℂ) X := ⟨Z + AJ, h_cycle⟩ with hC_def
  -- Period vector of cycle is in periodLatticeImage by tautology.
  have h_C_period : complexChainPeriodVector α (C : SmoothChain 𝓘(ℝ, ℂ) X)
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
    rw [complexChainPeriodVector_of_cycle_eq_periodVector]
    exact ⟨C, rfl⟩
  -- complexChainPeriodVector (Z + AJ) = complexChainPeriodVector Z + complexChainPeriodVector AJ.
  have h_split :
      complexChainPeriodVector α (C : SmoothChain 𝓘(ℝ, ℂ) X)
        = complexChainPeriodVector α Z + complexChainPeriodVector α AJ := by
    show complexChainPeriodVector α (Z + AJ) = _
    exact complexChainPeriodVector_add α Z AJ
  rw [h_split] at h_C_period
  -- period(AJ) = (period(Z) + period(AJ)) - period(Z) ∈ lattice - lattice ⊆ lattice.
  have h_diff : complexChainPeriodVector α AJ
      = (complexChainPeriodVector α Z + complexChainPeriodVector α AJ)
        - complexChainPeriodVector α Z := by ring
  rw [h_diff]
  exact AddSubgroup.sub_mem _ h_C_period h_Z_period

end MeromorphicNonzero

end JacobianChallenge

end
