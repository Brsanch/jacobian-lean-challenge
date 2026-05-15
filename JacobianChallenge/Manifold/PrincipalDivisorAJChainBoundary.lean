/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition
import JacobianChallenge.Manifold.ResidueTheoremUnconditional

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Boundary identity for the principal-divisor AJ chain

For any divisor `D : Div X` of degree zero,
`boundary (B.principalDivisorAJChain D)` evaluated at any point `y` returns
`(D : X → ℤ) y`. The argument is pure `ℤ`-linearity:

* `principalDivisorAJChain D = ∑ x ∈ D.supportFinset,
    D(x) • single (B.pathFromBase x)`;
* `boundary (single (B.pathFromBase x)) = δ_x − δ_{basePoint}` using
  `B.src_eq` and `B.tgt_eq`;
* therefore
  `boundary (principalDivisorAJChain D)
      = (∑ x ∈ S, D(x) • δ_x) − D.degree • δ_{basePoint}`;
* at `D.degree = 0` the second term vanishes and the first evaluates to
  `D y` pointwise (whether or not `y ∈ supportFinset`).

The corollary `boundary_principalDivisorAJChain_principalDivisorMap`
specialises `D := principalDivisorMap f` and discharges the degree
hypothesis via the in-tree unconditional `JacobianChallenge.residue_theorem`.

This file discharges the `h_AJ_boundary` named hypothesis of
`MeromorphicNonzeroAbelGeneratorFromLevelSet.lean`'s structural
reduction `abelGeneratorPeriodCondition_of_levelSet_lattice`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module Finset

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Boundary identity at a degree-zero divisor.** For any `D : Div X`
with `D.degree = 0`,
`(SmoothChain.boundary (B.principalDivisorAJChain D)).toFun y = D y`
pointwise. -/
theorem boundary_principalDivisorAJChain_apply_of_degree_zero
    (B : AbelJacobiInput α h) (D : Div X) (hD : D.degree = 0) (y : X) :
    (SmoothChain.boundary (B.principalDivisorAJChain D)).toFun y
      = (D : X → ℤ) y := by
  classical
  show SmoothChain.boundary (B.principalDivisorAJChain D) y = _
  unfold AbelJacobiInput.principalDivisorAJChain
  rw [map_sum, Finsupp.finset_sum_apply]
  have hsimp : ∀ x ∈ D.supportFinset,
      (SmoothChain.boundary
          (((D : X → ℤ) x) • SmoothChain.single (B.pathFromBase x))) y
        = ((D : X → ℤ) x) * ((if x = y then (1 : ℤ) else 0)
            - if B.basePoint = y then (1 : ℤ) else 0) := by
    intro x _
    rw [show SmoothChain.boundary
          (((D : X → ℤ) x) • SmoothChain.single (B.pathFromBase x))
        = ((D : X → ℤ) x) • SmoothChain.boundary
            (SmoothChain.single (B.pathFromBase x)) from
      (SmoothChain.boundary).map_smul _ _]
    rw [SmoothChain.boundary_single]
    show ((D : X → ℤ) x) • SmoothChain.boundarySingle (B.pathFromBase x) y = _
    unfold SmoothChain.boundarySingle
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
        B.tgt_eq x, B.src_eq x, smul_eq_mul]
  rw [Finset.sum_congr rfl hsimp]
  have hsplit : ∀ x ∈ D.supportFinset,
      ((D : X → ℤ) x) * ((if x = y then (1 : ℤ) else 0)
          - if B.basePoint = y then (1 : ℤ) else 0)
        = ((D : X → ℤ) x) * (if x = y then (1 : ℤ) else 0)
          - ((D : X → ℤ) x) * (if B.basePoint = y then (1 : ℤ) else 0) := by
    intro x _; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have hB : (∑ x ∈ D.supportFinset,
        ((D : X → ℤ) x) * (if B.basePoint = y then (1 : ℤ) else 0))
      = D.degree * (if B.basePoint = y then (1 : ℤ) else 0) := by
    rw [← Finset.sum_mul]
    rfl
  rw [hB, hD, zero_mul, sub_zero]
  by_cases hy : y ∈ D.supportFinset
  · rw [Finset.sum_eq_single y]
    · rw [if_pos rfl, mul_one]
    · intro x _ hxy
      rw [if_neg hxy, mul_zero]
    · intro hne; exact absurd hy hne
  · rw [Div.apply_eq_zero_of_notMem_supportFinset hy]
    apply Finset.sum_eq_zero
    intro x hxS
    have hxy : x ≠ y := fun heq => hy (heq ▸ hxS)
    rw [if_neg hxy, mul_zero]

/-- **Specialisation to `principalDivisorMap f`.** The residue theorem on
a compact connected Riemann surface (`JacobianChallenge.residue_theorem`)
gives `(principalDivisorMap f).degree = 0`, so the boundary of the
principal-divisor AJ chain for `principalDivisorMap f` equals
`principalDivisorMap f` pointwise. -/
theorem boundary_principalDivisorAJChain_principalDivisorMap
    (B : AbelJacobiInput α h) (f : MeromorphicNonzero X) (y : X) :
    (SmoothChain.boundary
        (B.principalDivisorAJChain (principalDivisorMap f))).toFun y
      = ((principalDivisorMap f : X → ℤ) y) :=
  boundary_principalDivisorAJChain_apply_of_degree_zero B
    (principalDivisorMap f) (JacobianChallenge.residue_theorem f) y

end AbelJacobiInput

end JacobianChallenge

end
