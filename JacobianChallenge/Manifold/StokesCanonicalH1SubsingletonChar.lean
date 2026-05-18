/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.StokesCanonicalClosedForms

set_option linter.unusedSectionVars false

/-! # `Subsingleton canonical-H1 ↔ stokesBoundaries = ⊤`

The canonical Stokes H₁ quotient
`(StokesBoundaryInvariance.canonical I X).H1
  = SmoothCycle I X ⧸ stokesBoundaries I X`
is subsingleton if and only if `stokesBoundaries I X = ⊤` as an
`AddSubgroup (SmoothCycle I X)`. Both express the same classical
content: every smooth 1-cycle is a smooth 2-chain boundary, i.e.
`H₁(X; ℤ) = 0` in smooth singular homology.

This file ships the characterization, which factors the "H₁ = 0
at genus 0" classical input through a SmoothCycle-level statement
that's cleaner to reason about directly.

## What this file ships

* `subsingleton_canonical_H1_iff_stokesBoundaries_eq_top` — the
  characterization.
* `subsingleton_canonical_H1_of_stokesBoundaries_eq_top` — easier
  direction.
* `stokesBoundaries_eq_top_of_subsingleton_canonical_H1` — harder
  direction.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **`stokesBoundaries = ⊤` ⇒ canonical H₁ subsingleton.** The
canonical H₁ quotient by the top subgroup is subsingleton. -/
theorem subsingleton_canonical_H1_of_stokesBoundaries_eq_top
    (h : stokesBoundaries I X = ⊤) :
    Subsingleton (StokesBoundaryInvariance.canonical I X).H1 := by
  -- The quotient of any group by the top subgroup is subsingleton.
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂' a b ?_
  intro c₁ c₂
  -- Goal: QuotientAddGroup.mk c₁ = QuotientAddGroup.mk c₂ in
  -- SmoothCycle / (canonical _).boundaries.
  refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
  -- `(canonical I X).boundaries = stokesBoundaries I X = ⊤`,
  -- so `c₁ - c₂ ∈ ⊤` is trivial.
  rw [StokesBoundaryInvariance.canonical_boundaries, h]
  exact AddSubgroup.mem_top _

/-- **Canonical H₁ subsingleton ⇒ `stokesBoundaries = ⊤`.** If the
canonical H₁ quotient is subsingleton, then every smooth 1-cycle is
a smooth 2-chain boundary. -/
theorem stokesBoundaries_eq_top_of_subsingleton_canonical_H1
    [hsub : Subsingleton (StokesBoundaryInvariance.canonical I X).H1] :
    stokesBoundaries I X = ⊤ := by
  rw [eq_top_iff]
  intro c _
  -- `c : SmoothCycle I X`. Want `c ∈ stokesBoundaries I X`.
  show c ∈ (StokesBoundaryInvariance.canonical I X).boundaries
  -- In `QuotientAddGroup` form: `mk c = mk 0` (by subsingleton) iff
  -- `c - 0 ∈ boundaries`, iff `c ∈ boundaries`.
  -- Identify the quotient with `.H1` so the subsingleton instance applies.
  have h_mk_eq :
      ((StokesBoundaryInvariance.canonical I X).proj c
          : (StokesBoundaryInvariance.canonical I X).H1)
        = (StokesBoundaryInvariance.canonical I X).proj 0 :=
    Subsingleton.elim _ _
  have h_sub : c - 0 ∈ (StokesBoundaryInvariance.canonical I X).boundaries :=
    QuotientAddGroup.eq_iff_sub_mem.mp h_mk_eq
  rwa [sub_zero] at h_sub

/-- **The characterization.** -/
theorem subsingleton_canonical_H1_iff_stokesBoundaries_eq_top :
    Nonempty (Subsingleton (StokesBoundaryInvariance.canonical I X).H1)
      ↔ stokesBoundaries I X = ⊤ := by
  refine ⟨fun ⟨hsub⟩ => ?_, fun h => ?_⟩
  · exact stokesBoundaries_eq_top_of_subsingleton_canonical_H1
  · exact ⟨subsingleton_canonical_H1_of_stokesBoundaries_eq_top h⟩

end JacobianChallenge

end
