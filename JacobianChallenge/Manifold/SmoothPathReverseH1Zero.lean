/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary
import JacobianChallenge.Manifold.StokesCanonicalClosedForms

set_option linter.unusedSectionVars false

/-! # In canonical H₁: `[single γ + single γ.reverse] = 0`

Corollary of `single_smoothPath_plus_reverse_mem_stokesBoundaries`
(chip 18): the cycle `single γ + single γ.reverse`, projected to the
canonical Stokes H₁ quotient
`(StokesBoundaryInvariance.canonical I X).H1
   = SmoothCycle I X ⧸ stokesBoundaries I X`,
is zero.

Geometric content: in the canonical Stokes-homology quotient on
**any** smooth manifold `X`, every smooth path's reverse cancels it.
Combined with the H₁-subsingleton-iff-stokesBoundaries-eq-top
characterization, the gap between the canonical Stokes-homology and
the full H₁(X; ℤ) is precisely the simply-connectedness content.

## What this file ships

* `proj_single_smoothPath_plus_reverse_eq_zero` — the H₁-projection
  of `single γ + single γ.reverse` is zero.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **Canonical-H₁ projection of `single γ + single γ.reverse` is
zero.** Direct consequence of `single_smoothPath_plus_reverse_mem_stokesBoundaries`
(chip 18) — being in `stokesBoundaries = (canonical I X).boundaries`,
the SmoothCycle projects to zero under
`(canonical I X).proj = QuotientAddGroup.mk' _`. -/
theorem proj_single_smoothPath_plus_reverse_eq_zero
    (γ : SmoothPath I X) :
    ((StokesBoundaryInvariance.canonical I X).proj
        (single_smoothPath_plus_reverse_smoothCycle γ)
      : (StokesBoundaryInvariance.canonical I X).H1) = 0 := by
  -- A quotient-class is zero iff its representative lies in the
  -- boundary subgroup: use `QuotientAddGroup.eq_zero_iff`.
  show (QuotientAddGroup.mk (single_smoothPath_plus_reverse_smoothCycle γ)
      : (StokesBoundaryInvariance.canonical I X).H1) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact single_smoothPath_plus_reverse_mem_stokesBoundaries γ

end JacobianChallenge

end
