/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPoint
import JacobianChallenge.Divisor

set_option diagnostics.threshold 100

/-! # PL-4-D: Divisor-level Abel-Jacobi map

Extends the pointwise `abelJacobiPoint : X → AnalyticJacobian` to formal
divisors `Div X = Function.locallyFinsuppWithin (univ : Set X) ℤ`.

On a compact Hausdorff space, every divisor has finite support (already
used in `Div.degree` for the same reason), so the ℤ-linear extension is
a finite sum:

    `abelJacobiDiv B D := ∑ x ∈ D.supportFinset, (D : X → ℤ) x • B.abelJacobiPoint x`.

## What this file delivers

* `abelJacobiDiv B D : AnalyticJacobian` — divisor-level AJ.
* `abelJacobiDiv_zero`, `abelJacobiDiv_add`, `abelJacobiDiv_eq_sum_of_supportFinset_subset`
  — basic identities mirroring `Div.degree`'s proofs.
* `abelJacobiDivHom B : Div X →+ AnalyticJacobian` — bundled additive
  hom version.

The Abel-Jacobi map of interest is the **restriction to degree-0
divisors**:

* `abelJacobiDiv0Hom B : Div0 X →+ AnalyticJacobian` — restricted to
  `Div0 X := (Div.degreeHom).ker`.

The restriction makes the base-point dependence cancel: if the
coefficients of `D` sum to zero, swapping base point translates each
`abelJacobiPoint` by a fixed class, but the sum is unchanged. (This
cancellation property is a follow-up cleanup lemma.)

After this chip, the remaining work for full Abel-Jacobi:

* **PL-4-E (Abel's theorem):** `abelJacobiDiv0Hom B` vanishes on
  principal divisors `PrincDiv X`. Requires Stokes on a 2-chain
  representing the principal divisor.
* **PL-4-F (descent):** `abelJacobi : Pic0 X →+ AnalyticJacobian` —
  quotient by `PrincDiv X`.
* **PL-4-G (iso):** injectivity + surjectivity = Jacobi inversion.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Divisor-level Abel-Jacobi.** Sum of `n • abelJacobiPoint x` over
the (finite, on compact `X`) support of `D`. -/
noncomputable def abelJacobiDiv (B : AbelJacobiInput α h) (D : Div X) :
    AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • B.abelJacobiPoint x

/-- **Compute over a containing finset.** Values outside the support
contribute zero. -/
lemma abelJacobiDiv_eq_sum_of_supportFinset_subset
    (B : AbelJacobiInput α h) {D : Div X} {S : Finset X}
    (hS : D.supportFinset ⊆ S) :
    B.abelJacobiDiv D
      = ∑ x ∈ S, ((D : X → ℤ) x) • B.abelJacobiPoint x := by
  classical
  unfold abelJacobiDiv
  refine Finset.sum_subset hS ?_
  intro x _ hxS
  rw [Div.apply_eq_zero_of_notMem_supportFinset hxS, zero_smul]

@[simp] lemma abelJacobiDiv_zero (B : AbelJacobiInput α h) :
    B.abelJacobiDiv (0 : Div X) = 0 := by
  classical
  unfold abelJacobiDiv
  have hsupp : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
    ext x; simp
  have hempty : (0 : Div X).supportFinset = (∅ : Finset X) := by
    unfold Div.supportFinset
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' : x ∈ ((0 : Div X) : X → ℤ).support :=
      (Set.Finite.mem_toFinset _).1 hx
    rw [hsupp] at hx'
    exact hx'.elim
  rw [hempty]
  exact Finset.sum_empty

lemma abelJacobiDiv_add (B : AbelJacobiInput α h) (D₁ D₂ : Div X) :
    B.abelJacobiDiv (D₁ + D₂) = B.abelJacobiDiv D₁ + B.abelJacobiDiv D₂ := by
  classical
  set S : Finset X :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have h1 : D₁.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h2 : D₂.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_right _ hx
  rw [B.abelJacobiDiv_eq_sum_of_supportFinset_subset h12,
      B.abelJacobiDiv_eq_sum_of_supportFinset_subset h1,
      B.abelJacobiDiv_eq_sum_of_supportFinset_subset h2]
  have hpt : ∀ x : X, ((D₁ + D₂ : Div X) : X → ℤ) x
      = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
    intro x
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [show (∑ x ∈ S, ((D₁ + D₂ : Div X) : X → ℤ) x • B.abelJacobiPoint x)
        = ∑ x ∈ S, ((D₁ : X → ℤ) x + (D₂ : X → ℤ) x) • B.abelJacobiPoint x from by
        refine Finset.sum_congr rfl ?_
        intro x _; rw [hpt]]
  -- Distribute `(a + b) • v = a • v + b • v` and apply `Finset.sum_add_distrib`.
  rw [show (∑ x ∈ S, ((D₁ : X → ℤ) x + (D₂ : X → ℤ) x) • B.abelJacobiPoint x)
        = ∑ x ∈ S, ((D₁ : X → ℤ) x • B.abelJacobiPoint x
          + (D₂ : X → ℤ) x • B.abelJacobiPoint x) from by
        refine Finset.sum_congr rfl ?_
        intro x _; rw [add_smul]]
  exact Finset.sum_add_distrib

/-- **Bundled divisor-level Abel-Jacobi.** -/
noncomputable def abelJacobiDivHom (B : AbelJacobiInput α h) :
    Div X →+ AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h where
  toFun := B.abelJacobiDiv
  map_zero' := B.abelJacobiDiv_zero
  map_add' := B.abelJacobiDiv_add

@[simp] lemma abelJacobiDivHom_apply (B : AbelJacobiInput α h) (D : Div X) :
    B.abelJacobiDivHom D = B.abelJacobiDiv D := rfl

/-- **Restriction to degree-zero divisors.** Composes `abelJacobiDivHom`
with the inclusion `Div0 X ↪ Div X`. -/
noncomputable def abelJacobiDiv0Hom (B : AbelJacobiInput α h) :
    Div0 X →+ AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  B.abelJacobiDivHom.comp (Div0 X).subtype

@[simp] lemma abelJacobiDiv0Hom_apply (B : AbelJacobiInput α h) (D : Div0 X) :
    B.abelJacobiDiv0Hom D = B.abelJacobiDiv (D : Div X) := rfl

end AbelJacobiInput

end JacobianChallenge

end
