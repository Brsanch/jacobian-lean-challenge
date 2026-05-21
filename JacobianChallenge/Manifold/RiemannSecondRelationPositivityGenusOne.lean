/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityNamed
import JacobianChallenge.Manifold.RiemannBilinearMatrixPosGenusOne
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticOneSymbolic

set_option linter.unusedSectionVars false

/-! # `RiemannSecondRelationPositivity` at genus 1 from lattice orientation

At `genus X = 1`, RSRP reduces (via the in-tree
`riemannBilinearMatrixPos_of_diagonal_pos_genus_one` and
`iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_im / _re`)
to a **single lattice-orientation scalar**

  `0 < Im(star (pmat k₀ i₀) · pmat k₁ i₀)`

for `k₀, k₁ : Fin (2 * genus X)` with `val 0, 1` (the two
homology basis indices). Classically this is `Im(τ) > 0` where
`τ = pmat k₁ i₀ / pmat k₀ i₀`.

This is the **substantive analytic content** at genus 1 — the
lattice-orientation condition that's unconditional for `T_L` (via
chip 19s's positively-oriented ℤ-basis) and represents the universal
period relation at g=1 for general `X`.

## What this file ships

* `riemannSecondRelationPositivity_of_genus_one_of_lattice_orientation`
  — RSRP from `genus X = 1` + the single positivity scalar input.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannSecondRelationPositivity` at `genus X = 1` from the
single lattice-orientation scalar.**

Substantive content at genus 1. Inputs:
* `h_g : genus X = 1`.
* `k₀, k₁ : Fin (2 * genus X)` with `val 0, 1` — the two homology
  basis cycle indices.
* `i₀ : Fin (genus X)` — the unique 1-form basis index at g=1.
* `h_orient : 0 < Im(star (pmat k₀ i₀) · pmat k₁ i₀)` — the
  lattice-orientation scalar (the classical `Im(τ) > 0`).

Outputs: RSRP on `data, basis_ω, cycleGens`. -/
theorem riemannSecondRelationPositivity_of_genus_one_of_lattice_orientation
    (h_g : JacobianChallenge.genus X = 1)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (k₀ k₁ : Fin (2 * JacobianChallenge.genus X))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_orient :
      0 < (star (periodMatrix data basis_ω cycleGens k₀ i₀)
            * periodMatrix data basis_ω cycleGens k₁ i₀).im) :
    RiemannSecondRelationPositivity data basis_ω cycleGens := by
  -- Apply chip 19g at the genus-X matrix.
  apply riemannBilinearMatrixPos_of_diagonal_pos_genus_one
    (g := JacobianChallenge.genus X) h_g
  · -- diagonal .im = 0: chip 19i's genus-X variant.
    intro i
    exact iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_im h_g _ i
  · -- diagonal 0 < .re: chip 19i's `_re` + h_orient + 2 · _ > 0.
    intro i
    haveI : Subsingleton (Fin (JacobianChallenge.genus X)) := by
      rw [h_g]; infer_instance
    have hi : i = i₀ := Subsingleton.elim _ _
    rw [hi]
    rw [iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_re h_g
        (periodMatrix data basis_ω cycleGens) i₀ k₀ k₁ h_k₀ h_k₁]
    linarith

end JacobianChallenge

end
