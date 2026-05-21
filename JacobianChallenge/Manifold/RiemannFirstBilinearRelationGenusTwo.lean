/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationNamed

set_option linter.unusedSectionVars false

/-! # `RiemannFirstBilinearRelation` at genus 2 from a single scalar

At `JacobianChallenge.genus X = 2`, the space `HolomorphicOneForm X`
is 2-dimensional over `ℂ`. With a chosen basis `α : Basis (Fin 2) ℂ
(HolomorphicOneForm X)`, every ω decomposes as
`(α.repr ω 0) • α 0 + (α.repr ω 1) • α 1`. The bilinear form
`Q J cycleGens ω₀ ω₁` expands into four terms:

  `Q J cycleGens ω₀ ω₁
    = c₀₀ · c₁₀ · Q J cycleGens (α 0) (α 0)
    + c₀₀ · c₁₁ · Q J cycleGens (α 0) (α 1)
    + c₀₁ · c₁₀ · Q J cycleGens (α 1) (α 0)
    + c₀₁ · c₁₁ · Q J cycleGens (α 1) (α 1)`

(where `c_ij = α.repr ω_i j`). Under antisymmetric `J`:

* Diagonal terms `Q J cycleGens (α 0) (α 0) = Q J cycleGens (α 1) (α 1)
  = 0` (chip 7).
* `Q J cycleGens (α 1) (α 0) = - Q J cycleGens (α 0) (α 1)`
  (chip 6 antisymmetry).

So `Q J cycleGens ω₀ ω₁ = (c₀₀ · c₁₁ - c₀₁ · c₁₀) · Q J cycleGens (α 0) (α 1)`,
which vanishes for all ω₀, ω₁ ⟺ `Q J cycleGens (α 0) (α 1) = 0`.

This is the chip 9 named-hypothesis form of chip 20h
(`riemannBilinearFirstRelation_iff_single_scalar_zero_genus_two`).

## What this file ships

* `riemannFirstBilinearRelation_of_genus_two_of_single_scalar_zero`
  — at `genus X = 2 + Jᵀ = -J`, RFBR follows from
  `Q J cycleGens (α 0) (α 1) = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannFirstBilinearRelation` at `genus X = 2` from the single
scalar `Q J cycleGens (α 0) (α 1) = 0`.**

Bilinear expansion against the chosen basis `α : Basis (Fin 2) ℂ
(HolomorphicOneForm X)`, using chip 7 to kill diagonal entries and
chip 6 antisymmetry to fold `Q J (α 1) (α 0)` into `-Q J (α 0) (α 1)`. -/
theorem riemannFirstBilinearRelation_of_genus_two_of_single_scalar_zero
    (_h_genus : JacobianChallenge.genus X = 2)
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (α₂ : Basis (Fin 2) ℂ (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_scalar :
      riemannBilinearPeriodForm cycleGens J (α₂ 0) (α₂ 1) = 0) :
    RiemannFirstBilinearRelation cycleGens J := by
  intro ω₀ ω₁
  -- Decompose ω₀ = c00 • α₂ 0 + c01 • α₂ 1 and ω₁ = c10 • α₂ 0 + c11 • α₂ 1.
  have h_ω₀ :
      ω₀ = (α₂.repr ω₀ 0) • α₂ 0 + (α₂.repr ω₀ 1) • α₂ 1 := by
    have := α₂.sum_repr ω₀
    rw [Fin.sum_univ_two] at this
    exact this.symm
  have h_ω₁ :
      ω₁ = (α₂.repr ω₁ 0) • α₂ 0 + (α₂.repr ω₁ 1) • α₂ 1 := by
    have := α₂.sum_repr ω₁
    rw [Fin.sum_univ_two] at this
    exact this.symm
  rw [h_ω₀, h_ω₁]
  -- Expand Q via bilinearity (add_left, smul_left on first arg,
  -- add_right, smul_right on second arg).
  rw [riemannBilinearPeriodForm_add_left,
      riemannBilinearPeriodForm_smul_left,
      riemannBilinearPeriodForm_smul_left]
  rw [riemannBilinearPeriodForm_add_right (cycleGens := cycleGens) (J := J),
      riemannBilinearPeriodForm_add_right (cycleGens := cycleGens) (J := J),
      riemannBilinearPeriodForm_smul_right,
      riemannBilinearPeriodForm_smul_right,
      riemannBilinearPeriodForm_smul_right,
      riemannBilinearPeriodForm_smul_right]
  -- Diagonal entries vanish via chip 7.
  rw [riemannBilinearPeriodForm_self_eq_zero cycleGens hJ (α₂ 0)]
  rw [riemannBilinearPeriodForm_self_eq_zero cycleGens hJ (α₂ 1)]
  -- Q (α 1) (α 0) = - Q (α 0) (α 1) via chip 6 antisymmetry.
  rw [riemannBilinearPeriodForm_antisymm cycleGens hJ (α₂ 1) (α₂ 0)]
  -- Q (α 0) (α 1) = 0 by the named scalar input.
  rw [h_scalar]
  ring

end JacobianChallenge

end
