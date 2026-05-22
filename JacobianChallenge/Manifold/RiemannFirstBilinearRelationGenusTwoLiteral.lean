/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationGenusTwo
import JacobianChallenge.Manifold.PeriodMatrixBilinearStandardSymplecticTwo
import JacobianChallenge.Manifold.PeriodMatrix
import JacobianChallenge.Manifold.RiemannBilinearPeriodForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `RiemannFirstBilinearRelation` at genus 2 from a single literal period-matrix scalar

At `genus X = 2`, `RiemannFirstBilinearRelation` reduces to a single
explicit period-matrix entry vanishing. Using the closed form from
`periodMatrixBilinear_standardSymplectic_two_apply`, the substantive
scalar identity is

  `pm_{0,0}·pm_{2,1} + pm_{1,0}·pm_{3,1}
   − pm_{2,0}·pm_{0,1} − pm_{3,0}·pm_{1,1} = 0`,

where `pm := periodMatrix data basis_ω cycleGens : Matrix (Fin 4)
(Fin 2) ℂ` (under `genus X = 2`).

## What ships

* `riemannFirstBilinearRelation_of_genus_two_literal_scalar` — RBFR
  at `genus X = 2` from the single literal scalar identity, via the
  in-tree `riemannFirstBilinearRelation_of_genus_two_of_single_scalar_zero`
  composed with the closed form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **RBFR at `genus X = 2` from the explicit period-matrix scalar.** -/
theorem riemannFirstBilinearRelation_of_genus_two_literal_scalar
    (h_genus : JacobianChallenge.genus X = 2)
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (i₀ i₁ : Fin (JacobianChallenge.genus X))
    (h_i₀ : i₀.val = 0) (h_i₁ : i₁.val = 1)
    (h_scalar :
      riemannBilinearPeriodForm cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (basis_ω i₀) (basis_ω i₁) = 0) :
    RiemannFirstBilinearRelation cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) := by
  -- At g = 2, Fin (genus X) has exactly 2 elements. i₀, i₁ play the roles
  -- of "0" and "1". By `Subsingleton (Fin 2)` is FALSE — Fin 2 has 2 elements.
  -- But via the existing `riemannFirstBilinearRelation_of_genus_two_of_single_scalar_zero`,
  -- the scalar form is `Q (α 0) (α 1) = 0` for some basis. We map basis_ω to
  -- a Fin 2-basis by transport.
  -- Strategy: build a Fin 2-basis from basis_ω + the equality genus X = 2.
  have h_2g : 2 * JacobianChallenge.genus X = 2 * 2 := by rw [h_genus]
  -- Construct a Basis (Fin 2) ℂ (HolomorphicOneForm X) from basis_ω.
  let α₂ : Basis (Fin 2) ℂ (HolomorphicOneForm X) :=
    basis_ω.reindex (finCongr h_genus)
  have h_α₂_0 : α₂ 0 = basis_ω i₀ := by
    show basis_ω.reindex (finCongr h_genus) 0 = basis_ω i₀
    rw [Basis.reindex_apply]
    congr 1
    apply Fin.ext
    show ((finCongr h_genus).symm 0).val = i₀.val
    rw [h_i₀]
    simp [finCongr]
  have h_α₂_1 : α₂ 1 = basis_ω i₁ := by
    show basis_ω.reindex (finCongr h_genus) 1 = basis_ω i₁
    rw [Basis.reindex_apply]
    congr 1
    apply Fin.ext
    show ((finCongr h_genus).symm 1).val = i₁.val
    rw [h_i₁]
    simp [finCongr]
  apply riemannFirstBilinearRelation_of_genus_two_of_single_scalar_zero
    h_genus α₂ cycleGens (standardSymplectic_antisymm _)
  rw [h_α₂_0, h_α₂_1]
  exact h_scalar

end JacobianChallenge

end
