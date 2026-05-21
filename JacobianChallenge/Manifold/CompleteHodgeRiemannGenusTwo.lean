/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromUpperTriangularStandard
import JacobianChallenge.Manifold.RiemannBilinearFirstRelationGenusTwo

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` at genus 2 from minimal inputs (chip 20r)

Specialization of chip 20p at `genus X = 2`:

  `CompleteHodgeRiemannHypothesis data basis_ω cycleGens`
  ⟸  (N 0 1 = 0 + 2 × 2 matrix PD)

where `N := pmatᵀ · standardSymplectic.cast · pmat` and `pmat` is the
period matrix. The first relation atom collapses to a *single* scalar
equation `N 0 1 = 0` at genus 2 (via chip 20h
`riemannBilinearFirstRelation_iff_single_scalar_zero_genus_two`).

This is the **minimal inputs form of CHRH at genus 2**:

* 1 scalar equation from the first relation;
* 2 × 2 Hermitian matrix positivity from the second relation.

Compare with the chip 19/20 chain at other low genera:

* `g = 0`: 0 inputs (vacuous, chip 20a);
* `g = 1`: 1 scalar positivity (diagonal, chip 19h);
* `g = 2`: 1 scalar zero + 2 × 2 Hermitian PD (this file);
* `g ≥ 3`: `g(g − 1)/2` scalar zeros + `g × g` Hermitian PD (chip 20p).

## What this file ships

* `completeHodgeRiemannHypothesis_of_standardSymplectic_genus_two` —
  the genus-2 specialization.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **CHRH at `genus X = 2` from a single scalar equation + 2 × 2
matrix positivity.** Specializes chip 20p using chip 20h's reduction
of the first relation at `g = 2` to the single entry `N 0 1 = 0`. -/
theorem completeHodgeRiemannHypothesis_of_standardSymplectic_genus_two
    (h_g : JacobianChallenge.genus X = 2)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (h_01 :
      ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic
              (JacobianChallenge.genus X)).map ((↑) : ℤ → ℂ)
        * periodMatrix data basis_ω cycleGens)
          (⟨0, by rw [h_g]; decide⟩ : Fin (JacobianChallenge.genus X))
          (⟨1, by rw [h_g]; decide⟩ : Fin (JacobianChallenge.genus X))
        = 0)
    (hPos : ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens)
                  (standardSymplectic (JacobianChallenge.genus X)))
              *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens)
                  (standardSymplectic (JacobianChallenge.genus X)))
              *ᵥ x)).re) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  -- Derive the full strict-upper-triangular condition from `h_01`
  -- via chip 20h's biconditional.
  have hFirst : RiemannBilinearFirstRelation data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) :=
    riemannBilinearFirstRelation_of_single_scalar_zero_genus_two
      h_g data basis_ω cycleGens
      (standardSymplectic_antisymm _) h_01
  have h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        ((periodMatrix data basis_ω cycleGens)ᵀ
            * (standardSymplectic
                (JacobianChallenge.genus X)).map ((↑) : ℤ → ℂ)
          * periodMatrix data basis_ω cycleGens) i j = 0 := by
    intro i j hij
    have hN := hFirst
    -- The first relation says the whole matrix is 0; in particular the (i, j) entry.
    have := congr_fun (congr_fun hN i) j
    simpa using this
  -- Now apply chip 20p.
  exact completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos
    data basis_ω cycleGens h_upper hPos

end JacobianChallenge

end
