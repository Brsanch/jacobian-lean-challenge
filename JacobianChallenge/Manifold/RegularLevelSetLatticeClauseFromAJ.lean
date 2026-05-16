/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RegularLevelSetChainBoundaryAJ
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition
import JacobianChallenge.Manifold.AbelLatticeWitnessFromRegular
import JacobianChallenge.Manifold.AbelJacobiPath

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `RegularLevelSetLatticeClause` from `AbelGeneratorPeriodCondition`

Structural reduction routing `RegularLevelSetLatticeClause X α h`
through the AJ-chain period condition `AbelGeneratorPeriodCondition B`
for any `B : AbelJacobiInput α h`.

The argument is the cycle witness `Z + AJ ∈ SmoothCycle` (from
`RegularLevelSetChainBoundaryAJ.lean`'s
`regularLevelSetChain_add_principalDivisorAJChain_mem_smoothCycle`).
Since `Z + AJ` is a smooth cycle, its period vector lies in
`periodLatticeImage`. Given that the AJ component's period is also in
the lattice (= `AbelGeneratorPeriodCondition B` applied to
`principalDivisorMap f`), the difference `period(Z) = period(Z + AJ) -
period(AJ)` lies in the lattice (`AddSubgroup.sub_mem`).

This is the missing piece in the structural chain: existing chips
gave `RegularLevelSetLatticeClause → AbelLatticeWitness → AbelHypothesis`,
and `abelGeneratorPeriodCondition_of_levelSet_lattice` gave the
converse `AbelLatticeWitness → AbelGeneratorPeriodCondition B`. This
chip closes the loop in the *other* direction: from
`AbelGeneratorPeriodCondition B` to `RegularLevelSetLatticeClause`,
making the two equivalent (modulo the regular-only restriction in the
latter).

**Consequence**: any future discharge of `AbelGeneratorPeriodCondition`
for a single `B` (e.g. via residue theorem on 1-forms applied to AJ
chains) immediately closes `RegularLevelSetLatticeClause`. At genus
zero, `AbelGeneratorPeriodCondition` is already trivially true, so this
chip closes the regular-case lattice clause unconditionally there too.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **`RegularLevelSetLatticeClause` from `AbelGeneratorPeriodCondition`.**

For any choice of base data `B : AbelJacobiInput α h`, the per-`f`
condition `AbelGeneratorPeriodCondition B` implies the regular-case
lattice clause via the cycle witness reduction. -/
theorem regularLevelSetLatticeClause_of_abelGeneratorPeriodCondition
    (B : AbelJacobiInput α h)
    (hAGen : AbelJacobiInput.AbelGeneratorPeriodCondition B) :
    RegularLevelSetLatticeClause X α h := by
  intro f hnc h0_reg h_inf_reg
  -- The cycle witness `Z + AJ` is a smooth cycle.
  set Z : SmoothChain 𝓘(ℝ, ℂ) X :=
    f.regularLevelSetChain hnc h0_reg h_inf_reg with hZ_def
  set AJ : SmoothChain 𝓘(ℝ, ℂ) X :=
    B.principalDivisorAJChain (principalDivisorMap f) with hAJ_def
  set C : SmoothCycle 𝓘(ℝ, ℂ) X :=
    f.regularLevelSetCycleWitness hnc h0_reg h_inf_reg B with hC_def
  -- Period vector of the cycle `C = Z + AJ` lies in `periodLatticeImage`.
  have h_C_period :
      complexChainPeriodVector α (C : SmoothChain 𝓘(ℝ, ℂ) X)
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
    rw [complexChainPeriodVector_of_cycle_eq_periodVector]
    exact ⟨C, rfl⟩
  -- Unfold `(C : SmoothChain) = Z + AJ` via the simp lemma on the witness.
  have h_C_unfold : (C : SmoothChain 𝓘(ℝ, ℂ) X) = Z + AJ :=
    f.regularLevelSetCycleWitness_coe hnc h0_reg h_inf_reg B
  rw [h_C_unfold, complexChainPeriodVector_add α] at h_C_period
  -- AJ period ∈ lattice by hypothesis.
  have h_AJ_period :
      complexChainPeriodVector α AJ
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α :=
    hAGen f
  -- period(Z) = period(Z+AJ) - period(AJ) ∈ lattice - lattice ⊆ lattice.
  have h_diff : complexChainPeriodVector α Z
      = (complexChainPeriodVector α Z + complexChainPeriodVector α AJ)
        - complexChainPeriodVector α AJ := by ring
  rw [h_diff]
  exact AddSubgroup.sub_mem _ h_C_period h_AJ_period

/-- **At genus zero, `RegularLevelSetLatticeClause` holds unconditionally.**

`AbelGeneratorPeriodCondition` is trivially true at genus zero
(`abelChainPeriodCondition_of_genus_zero` makes the period vector a
subsingleton); pre-composing with
`regularLevelSetLatticeClause_of_abelGeneratorPeriodCondition` closes
the regular-case lattice clause at genus zero.

(NB: an `AbelJacobiInput` for `X` is needed to instantiate `B`. At
genus zero, callers should supply this from the genus-zero scaffolding
in `AbelGeneratorGenusZero.lean`.) -/
theorem regularLevelSetLatticeClause_of_genus_zero
    (B : AbelJacobiInput α h)
    (hgenus : JacobianChallenge.genus X = 0) :
    RegularLevelSetLatticeClause X α h := by
  refine regularLevelSetLatticeClause_of_abelGeneratorPeriodCondition B ?_
  -- Subsingleton period vector at genus zero.
  intro f
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_pi_fin_genus_zero (X := X) hgenus
  have h0 : complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap f)) = 0 :=
    Subsingleton.elim _ _
  rw [h0]
  exact zero_mem _

end JacobianChallenge

end
