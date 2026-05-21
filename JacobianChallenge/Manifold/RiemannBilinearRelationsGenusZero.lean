/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearRelations
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `RiemannBilinearRelations` UNCONDITIONAL at genus 0 (chip 20b)

For any compact connected complex 1-manifold `X` with
`JacobianChallenge.genus X = 0`,
`RiemannBilinearRelations data basis_ω cycleGens` holds
unconditionally — the bundle is vacuous because every relevant
matrix is `Fin 0 × Fin 0` and the positivity quantifier ranges over
an empty type.

The chain (no orientation, no Hodge form choice, no
non-vacuous positivity content):

* `DiskChartCover.holomorphicOneFormFiniteDim_holds` ⟹
  `[FiniteDimensional ℂ (HolomorphicOneForm X)]` (unconditional).
* `holomorphicOneForm_subsingleton_of_genus_eq_zero` ⟹
  `[Subsingleton (HolomorphicOneForm X)]` once `genus X = 0`.
* `Subsingleton` + `Fin 0`-indexed matrices: every entry is 0,
  every quadratic form `star x ⬝ᵥ (M *ᵥ x)` with `x : Fin 0 → ℂ`
  collapses to `0` (only `x = 0` exists; the `≠ 0` premise is
  vacuous).

Parallel to chip 20a (`completeHodgeRiemannHypothesis_of_genus_eq_zero`),
which discharges the *full* Hodge-Riemann bundle (including the
Hodge form `H` and PD atom). This chip strips the `H` and PD and
keeps only the two matrix relations.

## What this file ships

* `riemannBilinearRelations_of_genus_eq_zero` — the headline.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannBilinearRelations` UNCONDITIONAL at `genus X = 0`.**

Takes `J := 0`. The first relation is `pmatᵀ · 0 · pmat = 0`,
trivially. The second relation:

* Hermitian conjunct: `i • (pmatᵀ · 0 · pmat).map star = 0` is
  trivially Hermitian (the zero matrix is Hermitian).
* Positivity conjunct: `∀ x : Fin g → ℂ, x ≠ 0 → ...`. At `g = 0`,
  `Fin g = Fin 0` is empty, so only `x = 0` exists; the `x ≠ 0`
  premise is unsatisfiable, making the implication vacuous. -/
theorem riemannBilinearRelations_of_genus_eq_zero
    (h_genus : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    RiemannBilinearRelations data basis_ω cycleGens := by
  haveI hFD : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  haveI hSub : Subsingleton (HolomorphicOneForm X) :=
    holomorphicOneForm_subsingleton_of_genus_eq_zero X h_genus
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_genus]; infer_instance
  -- Use J := 0. Both relations are vacuous on `Fin 0 × Fin 0` matrices.
  refine ⟨0, ?_, ?_⟩
  · -- First relation: `pmatᵀ · 0.cast · pmat = 0`.
    unfold RiemannBilinearFirstRelation
    simp [Matrix.map_zero]
  · -- Second relation: Hermitian + positivity, both vacuous.
    refine ⟨?_, ?_⟩
    · -- Hermitian: `i • (pmatᵀ · 0 · pmat.map star)` is the zero
      -- matrix (since J = 0), which is trivially Hermitian.
      simp [Matrix.IsHermitian]
    · -- Positivity quantifier: vacuous because `Fin g` is empty,
      -- so `x : Fin g → ℂ, x ≠ 0` has no inhabitant.
      intro x hx
      exact absurd (Subsingleton.elim x 0) hx

end JacobianChallenge

end
