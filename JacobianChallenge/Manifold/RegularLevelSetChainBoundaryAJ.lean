/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroConcreteLevelSetChain
import JacobianChallenge.Manifold.PrincipalDivisorAJChainBoundary
import JacobianChallenge.Manifold.ChainDifferenceCycle

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `regularLevelSetChain f + AJ-chain` is a smooth cycle

For `f : MeromorphicNonzero X` non-constant with `0` and `∞` regular,
the regular-level-set chain `Z := regularLevelSetChain f hnc h0 h∞`
satisfies `(boundary Z).toFun x = -((principalDivisorMap f) x)`
pointwise (chip `MeromorphicNonzeroConcreteLevelSetChain.lean`).

The AJ chain `AJ := B.principalDivisorAJChain (principalDivisorMap f)`
satisfies `(boundary AJ).toFun x = ((principalDivisorMap f) x)`
pointwise, by the unconditional residue theorem (chip
`PrincipalDivisorAJChainBoundary.lean`).

Adding pointwise:
`(boundary (Z + AJ)).toFun x = 0` for all `x`, so by `Finsupp.ext` the
boundary `Finsupp` is zero, and `Z + AJ ∈ SmoothCycle 𝓘(ℝ, ℂ) X`.

This file packages that observation as the reusable cycle witness
`regularLevelSetCycleWitness`. Downstream chips `r-3`–`r-7` consume
this to express the period vector of `regularLevelSetChain` modulo the
period lattice as the period vector of the AJ chain (which the residue
theorem then bridges back to the lattice).

This is the structural reduction that bypasses needing a "residue
theorem for meromorphic 1-forms on ℙ¹" as a fresh classical input —
the function-level `JacobianChallenge.residue_theorem` already in tree
suffices once routed through this cycle witness.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
variable {h : PeriodLatticeDiscretenessBundle
  (PeriodPairingData.ofSmoothCycle X) α}

/-! ## Boundary cancellation: pointwise -/

/-- **Pointwise boundary cancellation.** The sum
`regularLevelSetChain + principalDivisorAJChain (principalDivisorMap f)`
has boundary that vanishes at every point of `X`, by composing the two
in-tree pointwise boundary identities. -/
lemma boundary_regularLevelSetChain_add_principalDivisorAJChain_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (B : JacobianChallenge.AbelJacobiInput α h)
    (x : X) :
    (SmoothChain.boundary
        (f.regularLevelSetChain hnc h0_reg h_inf_reg
          + B.principalDivisorAJChain (principalDivisorMap f))).toFun x = 0 := by
  rw [SmoothChain.boundary_add]
  change ((SmoothChain.boundary (f.regularLevelSetChain hnc h0_reg h_inf_reg))
    + (SmoothChain.boundary
        (B.principalDivisorAJChain (principalDivisorMap f))) : X →₀ ℤ) x = 0
  rw [Finsupp.add_apply]
  change (SmoothChain.boundary (f.regularLevelSetChain hnc h0_reg h_inf_reg)).toFun x
      + (SmoothChain.boundary
          (B.principalDivisorAJChain (principalDivisorMap f))).toFun x = 0
  rw [f.boundary_regularLevelSetChain hnc h0_reg h_inf_reg x,
      AbelJacobiInput.boundary_principalDivisorAJChain_principalDivisorMap B f x]
  ring

/-! ## Boundary cancellation: as a `Finsupp` -/

/-- **Boundary cancellation as a Finsupp.** Lifts the pointwise
identity to a `Finsupp` equality via `Finsupp.ext`. -/
lemma boundary_regularLevelSetChain_add_principalDivisorAJChain
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (B : JacobianChallenge.AbelJacobiInput α h) :
    SmoothChain.boundary
        (f.regularLevelSetChain hnc h0_reg h_inf_reg
          + B.principalDivisorAJChain (principalDivisorMap f)) = 0 := by
  apply Finsupp.ext
  intro x
  exact f.boundary_regularLevelSetChain_add_principalDivisorAJChain_apply
    hnc h0_reg h_inf_reg B x

/-! ## The cycle witness -/

/-- **The cycle witness.** `regularLevelSetChain f + principalDivisorAJChain (principalDivisorMap f)`
is a smooth 1-cycle. -/
lemma regularLevelSetChain_add_principalDivisorAJChain_mem_smoothCycle
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (B : JacobianChallenge.AbelJacobiInput α h) :
    f.regularLevelSetChain hnc h0_reg h_inf_reg
        + B.principalDivisorAJChain (principalDivisorMap f)
      ∈ SmoothCycle 𝓘(ℝ, ℂ) X := by
  rw [SmoothCycle.mem_iff]
  exact f.boundary_regularLevelSetChain_add_principalDivisorAJChain
    hnc h0_reg h_inf_reg B

/-- **Cycle witness packaging.** Lift the boundary cancellation to a
`SmoothCycle` element. -/
noncomputable def regularLevelSetCycleWitness
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (B : JacobianChallenge.AbelJacobiInput α h) :
    SmoothCycle 𝓘(ℝ, ℂ) X :=
  ⟨f.regularLevelSetChain hnc h0_reg h_inf_reg
      + B.principalDivisorAJChain (principalDivisorMap f),
    f.regularLevelSetChain_add_principalDivisorAJChain_mem_smoothCycle
      hnc h0_reg h_inf_reg B⟩

@[simp] lemma regularLevelSetCycleWitness_coe
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (B : JacobianChallenge.AbelJacobiInput α h) :
    ((f.regularLevelSetCycleWitness hnc h0_reg h_inf_reg B :
        SmoothCycle 𝓘(ℝ, ℂ) X) : SmoothChain 𝓘(ℝ, ℂ) X)
      = f.regularLevelSetChain hnc h0_reg h_inf_reg
          + B.principalDivisorAJChain (principalDivisorMap f) := rfl

end MeromorphicNonzero

end JacobianChallenge

end
