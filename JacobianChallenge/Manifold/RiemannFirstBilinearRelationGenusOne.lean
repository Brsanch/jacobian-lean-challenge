/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationNamed
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false

/-! # `RiemannFirstBilinearRelation` at genus 1 from `Jᵀ = -J`

At `JacobianChallenge.genus X = 1`, the space `HolomorphicOneForm X`
is 1-dimensional over `ℂ`. Any two holomorphic 1-forms `ω₀, ω₁` are
proportional to a chosen basis vector `α`, so the bilinear form
`Q J cycleGens ω₀ ω₁` factors as

  `Q J cycleGens (c₀ • α) (c₁ • α) = c₀ · c₁ · Q J cycleGens α α`

via the ℂ-bilinearity of `Q` (chips 6's `_smul_left` /
`_smul_right`). For antisymmetric `J`, the diagonal entry
`Q J cycleGens α α = 0` (chip 7), so the whole product vanishes.

This validates the chip 9 named hypothesis at genus 1 from `Jᵀ = -J`
alone — mirroring chip 13's per-genus 1 first-relation discharge in
the in-tree chip 19/20 work. Together with chip 11 (genus 0
unconditional), the chip 9 hypothesis is unconditional at every
`genus ≤ 1`.

## What this file ships

* `riemannFirstBilinearRelation_of_genus_one` — discharge from
  `genus X = 1 + Jᵀ = -J`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannFirstBilinearRelation` at `genus X = 1` from
antisymmetric `J`.**

At genus 1, `HolomorphicOneForm X` is 1-dim ℂ (assumed via
`FiniteDimensional ℂ (HolomorphicOneForm X)` + `finrank = 1`). Any
two 1-forms are scalar multiples of a chosen basis vector `α`, and the
ℂ-bilinearity of `Q` plus chip 7's `_self_eq_zero` close the result.

The `FiniteDimensional` hypothesis is unconditional on every compact
connected complex 1-manifold via `DiskChartCover.holomorphicOneFormFiniteDim_holds`
+ the `finiteDimensional_of_HolomorphicOneFormFiniteDim` bridge — but
we leave it explicit here so the chip is decoupled from the Forster
chain. -/
theorem riemannFirstBilinearRelation_of_genus_one
    (h_genus : JacobianChallenge.genus X = 1)
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J) :
    RiemannFirstBilinearRelation cycleGens J := by
  -- Extract a basis of HolomorphicOneForm X over ℂ via Module.finBasis.
  have h_finrank :
      Module.finrank ℂ (HolomorphicOneForm X) = 1 := by
    rw [JacobianChallenge.genus] at h_genus
    exact h_genus
  let α : Basis (Fin 1) ℂ (HolomorphicOneForm X) :=
    Module.finBasisOfFinrankEq ℂ (HolomorphicOneForm X) h_finrank
  intro ω₀ ω₁
  -- Express ω₀ and ω₁ in terms of α 0 via the Fin 1 sum.
  have h_ω₀ : ω₀ = (α.repr ω₀ 0) • α 0 := by
    have := α.sum_repr ω₀
    rw [Fin.sum_univ_one] at this
    exact this.symm
  have h_ω₁ : ω₁ = (α.repr ω₁ 0) • α 0 := by
    have := α.sum_repr ω₁
    rw [Fin.sum_univ_one] at this
    exact this.symm
  rw [h_ω₀, h_ω₁]
  rw [riemannBilinearPeriodForm_smul_left, riemannBilinearPeriodForm_smul_right]
  rw [riemannBilinearPeriodForm_self_eq_zero cycleGens hJ (α 0)]
  ring

/-- **RFBR UNCONDITIONAL at `genus X = 1` for J := standardSymplectic 1.**

Specialization of `riemannFirstBilinearRelation_of_genus_one` absorbing
the `hJ` parameter via `standardSymplectic_antisymm`. -/
theorem riemannFirstBilinearRelation_of_genus_one_standardSymplectic
    (h_genus : JacobianChallenge.genus X = 1)
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    RiemannFirstBilinearRelation cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) :=
  riemannFirstBilinearRelation_of_genus_one h_genus cycleGens
    (standardSymplectic_antisymm (JacobianChallenge.genus X))

end JacobianChallenge

end
