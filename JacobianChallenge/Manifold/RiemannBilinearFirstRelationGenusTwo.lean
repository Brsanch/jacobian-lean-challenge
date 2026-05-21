/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearFirstRelationUpperTriangular

set_option linter.unusedSectionVars false

/-! # First relation at genus 2 from a single scalar equation (chip 20h)

Specialization of chip 20g at `g = 2`: the only strictly-upper-
triangular pair in `Fin 2 × Fin 2` is `(0, 1)`, so the first relation
reduces to a **single scalar equation**

  `((periodMatrix data α cycleGens)ᵀ · J.cast · periodMatrix) 0 1 = 0`.

Combined with anti-symmetry of `J`, this is the sharpest possible
discharge of the first relation at genus 2 from purely structural
content. The remaining open scalar equation is the classical
`∫_X ω_0 ∧ ω_1 = 0` content (Stokes + cup-product on the surface).

## What this file ships

* `riemannBilinearFirstRelation_iff_single_scalar_zero_genus_two` —
  the biconditional reduction at `g = 2`.
* `riemannBilinearFirstRelation_of_single_scalar_zero_genus_two` —
  the forward implication (the useful direction).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **First relation at `genus X = 2` from a single scalar equation.**

Specialization of chip 20g: at `g = 2`, the only strictly-upper-
triangular pair `(i, j)` with `i < j` in `Fin 2 × Fin 2` is `(0, 1)`.
So the off-diagonal/upper-triangular content collapses to a single
scalar equation. -/
theorem riemannBilinearFirstRelation_iff_single_scalar_zero_genus_two
    (h_g : JacobianChallenge.genus X = 2)
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J) :
    RiemannBilinearFirstRelation data α cycleGens J ↔
      ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * periodMatrix data α cycleGens)
          (⟨0, by rw [h_g]; decide⟩ : Fin (JacobianChallenge.genus X))
          (⟨1, by rw [h_g]; decide⟩ : Fin (JacobianChallenge.genus X))
        = 0 := by
  rw [riemannBilinearFirstRelation_iff_strictUpperTriangular_zero_of_antisymm
        data α cycleGens hJ]
  -- At `g = 2`, the strict-upper-triangular condition has a unique pair (0, 1).
  haveI : Fact (JacobianChallenge.genus X = 2) := ⟨h_g⟩
  set i₀ : Fin (JacobianChallenge.genus X) := ⟨0, by rw [h_g]; decide⟩
  set i₁ : Fin (JacobianChallenge.genus X) := ⟨1, by rw [h_g]; decide⟩
  constructor
  · intro h_upper
    have h_01_lt : i₀ < i₁ := by
      change (⟨0, _⟩ : Fin (JacobianChallenge.genus X))
        < (⟨1, _⟩ : Fin (JacobianChallenge.genus X))
      simp [Fin.lt_def]
    exact h_upper i₀ i₁ h_01_lt
  · intro h_01 i j hij
    have hi_lt : i.val < 2 := by rw [← h_g]; exact i.isLt
    have hj_lt : j.val < 2 := by rw [← h_g]; exact j.isLt
    have hij_val : i.val < j.val := hij
    have hi_val : i.val = 0 := by omega
    have hj_val : j.val = 1 := by omega
    have hi_eq : i = i₀ := by ext; exact hi_val
    have hj_eq : j = i₁ := by ext; exact hj_val
    rw [hi_eq, hj_eq]; exact h_01

/-- **Forward form: discharging the first relation at `g = 2` from
the single scalar equation.** -/
theorem riemannBilinearFirstRelation_of_single_scalar_zero_genus_two
    (h_g : JacobianChallenge.genus X = 2)
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_01 :
      ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * periodMatrix data α cycleGens)
          (⟨0, by rw [h_g]; decide⟩ : Fin (JacobianChallenge.genus X))
          (⟨1, by rw [h_g]; decide⟩ : Fin (JacobianChallenge.genus X))
        = 0) :
    RiemannBilinearFirstRelation data α cycleGens J :=
  (riemannBilinearFirstRelation_iff_single_scalar_zero_genus_two
    h_g data α cycleGens hJ).mpr h_01

end JacobianChallenge

end
