/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordantCongruence
import JacobianChallenge.Manifold.WordRepresentativeEmptyBasis

set_option linter.unusedSectionVars false

/-! # Constant-loop characterisation of `SmoothBordant`

Useful API: `SmoothBordant γ (constBasedLoopAt p₀)` is *equivalent*
to `γ.singleCycle ∈ stokesBoundaries`. This lets one freely switch
between the bordism predicate (preferred for word-representative
constructions) and the homological predicate (preferred for the
period-pairing side).

## What this file ships

* `SmoothBordant.const_iff_singleCycle_mem_stokesBoundaries` — the
  biconditional.
* `SmoothBordant.of_singleCycle_mem_stokesBoundaries` — the easy
  direction (`γ.cycle ∈ S → γ ~ const`).
* `singleCycle_mem_stokesBoundaries_of_bordant_const` — the reverse
  direction (`γ ~ const → γ.cycle ∈ S`).
* `basedSmoothLoopsBound_iff_forall_bordant_const` — the
  `BasedSmoothLoopsBoundHypothesis` predicate reformulated as
  "every based loop is bordant to the constant loop".

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace SmoothBordant

variable {p₀ : X}

/-- **Easy direction**: `γ.singleCycle ∈ stokesBoundaries` implies
`SmoothBordant γ (constBasedLoopAt p₀)`. The constant loop's `singleCycle`
is in `stokesBoundaries` (existing
`single_smoothPath_const_smoothCycle_mem_stokesBoundaries`), so the
difference `γ.cycle - const.cycle` is too. -/
theorem of_singleCycle_mem_stokesBoundaries
    {γ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀}
    (h_γ : γ.singleCycle ∈ stokesBoundaries 𝓘(ℝ, ℂ) X) :
    SmoothBordant γ (constBasedLoopAt p₀) := by
  unfold SmoothBordant
  have h_const : (constBasedLoopAt p₀).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    rw [constBasedLoopAt_singleCycle]
    exact single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  exact AddSubgroup.sub_mem _ h_γ h_const

/-- **Reverse direction**: `SmoothBordant γ (constBasedLoopAt p₀)` implies
`γ.singleCycle ∈ stokesBoundaries`. The bordism witness says
`γ.cycle - const.cycle ∈ stokes`; adding `const.cycle ∈ stokes`
recovers `γ.cycle ∈ stokes`. -/
theorem _root_.JacobianChallenge.singleCycle_mem_stokesBoundaries_of_bordant_const
    {γ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀}
    (h_bord : SmoothBordant γ (constBasedLoopAt p₀)) :
    γ.singleCycle ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
  unfold SmoothBordant at h_bord
  have h_const : (constBasedLoopAt p₀).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    rw [constBasedLoopAt_singleCycle]
    exact single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  have h_sum := AddSubgroup.add_mem _ h_bord h_const
  have h_eq : (γ.singleCycle - (constBasedLoopAt p₀).singleCycle)
      + (constBasedLoopAt p₀).singleCycle = γ.singleCycle := by abel
  rw [h_eq] at h_sum
  exact h_sum

/-- **The biconditional.** `SmoothBordant γ (constBasedLoopAt p₀)` iff
`γ.singleCycle ∈ stokesBoundaries`. -/
theorem const_iff_singleCycle_mem_stokesBoundaries
    {γ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀} :
    SmoothBordant γ (constBasedLoopAt p₀)
      ↔ γ.singleCycle ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
  ⟨singleCycle_mem_stokesBoundaries_of_bordant_const,
    of_singleCycle_mem_stokesBoundaries⟩

end SmoothBordant

/-! ## `BasedSmoothLoopsBoundHypothesis` as universal-bordism-to-const -/

/-- **`BasedSmoothLoopsBoundHypothesis` reformulated.** The hypothesis
"every smooth based loop has `singleCycle ∈ stokesBoundaries`" is
equivalent to "every smooth based loop is `SmoothBordant` to the
constant loop". -/
theorem basedSmoothLoopsBound_iff_forall_bordant_const (p₀ : X) :
    BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀
      ↔ ∀ γ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀,
          SmoothBordant γ (constBasedLoopAt p₀) := by
  constructor
  · intro h_bound γ
    apply SmoothBordant.of_singleCycle_mem_stokesBoundaries
    -- BasedSmoothLoopsBoundHypothesis says: ∀ γ smooth based loop at p₀,
    -- single_smoothLoop_smoothCycle γ _ ∈ stokesBoundaries.
    have h_γ_sing :
        γ.singleCycle
          = single_smoothLoop_smoothCycle γ.toPath γ.is_loop := by
      apply Subtype.ext
      rw [BasedLoopAt.singleCycle_coe, single_smoothLoop_smoothCycle_coe]
    rw [h_γ_sing]
    exact h_bound γ.toPath γ.toPath_src γ.toPath_tgt
  · intro h_bord γ h_src h_tgt
    -- Package γ as a BasedLoopAt at p₀.
    let γ_bl : BasedLoopAt 𝓘(ℝ, ℂ) X p₀ := ⟨γ, ⟨h_src, h_tgt⟩⟩
    have h_bord_γ : SmoothBordant γ_bl (constBasedLoopAt p₀) := h_bord γ_bl
    have h_γ_in :=
      singleCycle_mem_stokesBoundaries_of_bordant_const h_bord_γ
    have h_γ_sing :
        γ_bl.singleCycle
          = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) := by
      apply Subtype.ext
      rw [BasedLoopAt.singleCycle_coe, single_smoothLoop_smoothCycle_coe]
      rfl
    rw [h_γ_sing] at h_γ_in
    exact h_γ_in

end JacobianChallenge

end
