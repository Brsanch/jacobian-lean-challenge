/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetPrincipalDivisorIdentification
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition
import JacobianChallenge.Manifold.AbelJacobiPic0
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Step 9 — structural reduction: AbelGenerator from level-set lattice content

If for every `f : MeromorphicNonzero X` there exists a `SmoothChain Z`
with:
* `boundary Z = -principalDivisorMap f` (pointwise as Finsupp);
* `complexChainPeriodVector α Z ∈ periodLatticeImage`;

then `JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B` holds: the principal-divisor AJ
chain's period vector lies in the period lattice image.

## Argument

For each `f`, build the candidate cycle `C := Z + principalDivisorAJChain
B (principalDivisorMap f)`. Its boundary is

   `(-principalDivisorMap f) + (principalDivisorMap f) = 0`

(using `boundary (principalDivisorAJChain B D) = D as Finsupp` for
deg-0 `D`, which `principalDivisorMap f` is by the residue theorem).
So `C` is a `SmoothCycle`, and its period vector lies in
`periodLatticeImage` by tautology. Combined with the hypothesis that
`Z`'s period is in `periodLatticeImage`, the AJ chain's period is in
`periodLatticeImage` by linearity.

This file ships the **STRUCTURAL** reduction: the hypothesis "such
`Z` exists" is the named input. Discharging that hypothesis with the
level-set chain `levelSetChain f β` (whose boundary identification
with `-principalDivisorMap f` is `step 7d-d`, and whose period
lattice membership is the residual f-pushforward + Stokes content of
step 9 proper) closes C3 in full.

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

/-- **Structural reduction.** If a chain `Z` with `boundary Z = -principalDivisorMap f`
(pointwise) and `complexChainPeriodVector α Z ∈ periodLatticeImage` exists
for every `f`, then `JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B` holds. -/
theorem abelGeneratorPeriodCondition_of_levelSet_lattice
    (B : JacobianChallenge.AbelJacobiInput α h)
    (h_struct : ∀ f : MeromorphicNonzero X,
      ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
        (∀ x : X,
          (SmoothChain.boundary Z).toFun x
            = -((principalDivisorMap f : X → ℤ) x)) ∧
        complexChainPeriodVector α Z
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α)
    (h_AJ_boundary : ∀ f : MeromorphicNonzero X,
      ∀ x : X,
        (SmoothChain.boundary
            (B.principalDivisorAJChain (principalDivisorMap f))).toFun x
          = ((principalDivisorMap f : X → ℤ) x)) :
    JacobianChallenge.AbelJacobiInput.AbelGeneratorPeriodCondition B := by
  intro f
  obtain ⟨Z, h_Z_boundary, h_Z_period⟩ := h_struct f
  set AJ : SmoothChain 𝓘(ℝ, ℂ) X :=
    B.principalDivisorAJChain (principalDivisorMap f) with hAJ_def
  -- Boundary of Z + AJ is 0 (Finsupp-pointwise).
  have h_sum_boundary_pointwise : ∀ x : X,
      (SmoothChain.boundary (Z + AJ)).toFun x = 0 := by
    intro x
    rw [SmoothChain.boundary_add]
    change ((SmoothChain.boundary Z) + (SmoothChain.boundary AJ) : X →₀ ℤ) x = 0
    rw [Finsupp.add_apply]
    change (SmoothChain.boundary Z).toFun x + (SmoothChain.boundary AJ).toFun x = 0
    rw [h_Z_boundary x, h_AJ_boundary f x]
    ring
  -- Finsupp pointwise equality ⇒ Finsupp equality.
  have h_sum_boundary : SmoothChain.boundary (Z + AJ) = 0 := by
    apply Finsupp.ext
    intro x
    exact h_sum_boundary_pointwise x
  -- Z + AJ is a SmoothCycle.
  have h_cycle : Z + AJ ∈ SmoothCycle 𝓘(ℝ, ℂ) X := by
    rw [SmoothCycle.mem_iff]
    exact h_sum_boundary
  set C : SmoothCycle 𝓘(ℝ, ℂ) X := ⟨Z + AJ, h_cycle⟩
  -- Period vector of cycle ∈ periodLatticeImage.
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
  -- Combined: lhs (lattice) = period(Z) + period(AJ).
  rw [h_split] at h_C_period
  -- period(AJ) = period(Z+AJ) - period(Z) ∈ lattice - lattice ⊆ lattice.
  have h_AJ_period :
      complexChainPeriodVector α AJ
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
    have h_diff : complexChainPeriodVector α AJ
        = (complexChainPeriodVector α Z + complexChainPeriodVector α AJ)
          - complexChainPeriodVector α Z := by ring
    rw [h_diff]
    exact AddSubgroup.sub_mem _ h_C_period h_Z_period
  exact h_AJ_period

end MeromorphicNonzero

end JacobianChallenge

end
