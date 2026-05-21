/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannComplexTorus
import JacobianChallenge.Manifold.ComplexTorusOrientedBasis

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` on `T_L` UNCONDITIONAL (chip 19t)

The chip 19l theorem `completeHodgeRiemannHypothesis_complexTorus`
ships `CompleteHodgeRiemannHypothesis` on `T_L = ℂ ⧸ L` conditional
on the lattice-orientation input `0 < (star lam₁ · lam₂).im`. Chip
19s (`exists_positively_oriented_ZBasisOfL`) makes the existence
of a positively oriented ℤ-basis unconditional. This file composes
the two into an **unconditional `Nonempty`-form**:

  `∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),
    CompleteHodgeRiemannHypothesis … basis_g_dz
      ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex …).cycleGens`

— with no orientation hypothesis. This is the cleanest fully
unconditional statement of CHRH on the complex torus at the
basis_g_dz level.

## What this file ships

* `JacobianChallenge.ComplexTorus.exists_completeHodgeRiemannHypothesis_complexTorus`
  — the unconditional `Nonempty` headline.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`CompleteHodgeRiemannHypothesis` on `T_L` UNCONDITIONAL.**

The orientation hypothesis from chip 19l is discharged by chip 19s
(positively oriented ℤ-basis exists). Returns the witness pair
along with the CHRH statement. -/
theorem exists_completeHodgeRiemannHypothesis_complexTorus :
    ∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),
      CompleteHodgeRiemannHypothesis
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens) := by
  obtain ⟨lam₁, lam₂, hlam₁, hlam₂, _hZ, h_orient⟩ :=
    exists_positively_oriented_ZBasisOfL L
  exact ⟨lam₁, lam₂, hlam₁, hlam₂,
         completeHodgeRiemannHypothesis_complexTorus L lam₁ lam₂
           hlam₁ hlam₂ h_orient⟩

end ComplexTorus

end JacobianChallenge

end
