/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannGenusOneDiagonal
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticOneSymbolic

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` at genus 1 from a single orientation input (chip 19k)

Combines chips 19h (genus-1 1-input CHRH via diagonal positivity) and
19j (closed form for the diagonal at standardSymplectic g = 1) into a
single theorem: at `genus X = 1`, the full Hodge–Riemann bundle holds
from a **single classical input** — the lattice orientation

  `0 < Im(star (PeriodPairing data (cycleGens k₀) (basis_ω i₀)) ·
            PeriodPairing data (cycleGens k₁) (basis_ω i₀))`

for any choice of two distinct cycle indices `k₀ k₁ : Fin (2 * genus X)`
with `.val = 0` and `.val = 1` respectively, and any basis-coordinate
index `i₀ : Fin (genus X)`.

This is the **shortest 1-input reduction** of `CompleteHodgeRiemannHypothesis`
at genus 1. The remaining classical content is purely the lattice
orientation — the standard "positive area" condition on the period lattice.

## What this file ships

* `completeHodgeRiemannHypothesis_genus_one_of_orientation` — the
  single-input reduction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`CompleteHodgeRiemannHypothesis` at genus 1 from a lattice
orientation input.** Composes the genus-1 first-relation discharge,
the diagonal-positivity reduction at genus 1, and the closed form for
the diagonal at `J := standardSymplectic 1`. -/
theorem completeHodgeRiemannHypothesis_genus_one_of_orientation
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h_g : JacobianChallenge.genus X = 1)
    (k₀ k₁ : Fin (2 * JacobianChallenge.genus X))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_orient : 0 < (star (PeriodPairing data (cycleGens k₀) (basis_ω i₀)) *
                       PeriodPairing data (cycleGens k₁) (basis_ω i₀)).im) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  apply completeHodgeRiemannHypothesis_of_diagonal_pos_genus_one h_g
  · intro i
    exact iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_im h_g _ i
  · intro i
    have h_sub : Subsingleton (Fin (JacobianChallenge.genus X)) := by
      rw [h_g]; infer_instance
    have hi : i = i₀ := Subsingleton.elim _ _
    rw [hi]
    rw [iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_re h_g _ i₀ k₀ k₁ h_k₀ h_k₁]
    -- Goal: 0 < 2 * (star (pm k₀ i₀) * pm k₁ i₀).im
    -- where pm k₀ i₀ = PeriodPairing data (cycleGens k₀) (basis_ω i₀).
    have h_pm : ∀ k i,
        periodMatrix data basis_ω cycleGens k i
          = PeriodPairing data (cycleGens k) (basis_ω i) := fun _ _ => rfl
    rw [h_pm k₀ i₀, h_pm k₁ i₀]
    linarith

end JacobianChallenge

end
