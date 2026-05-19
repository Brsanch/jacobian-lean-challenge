/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomotopyStraightLineC
import JacobianChallenge.Manifold.WordRepresentativeEmptyBasis

set_option linter.unusedSectionVars false

/-! # `BasedSmoothLoopsBoundHypothesis` on `X = ℂ`, unconditional

The straight-line homotopy chip
(`SmoothHomotopyBasedLoop.straightLineC`) instantiates with the
constant-loop `constBasedLoopAt p₀` to give: every based loop `γ` at
`p₀ ∈ ℂ` is smoothly bordant to the constant loop at `p₀`. Combined
with the existing `single_smoothPath_const_smoothCycle_mem_stokesBoundaries`,
this discharges `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) ℂ p₀`
unconditionally:

> *Every smooth based loop's `single` lies in `stokesBoundaries`.*

Composed with `wordRepresentativeHypothesis_emptyBasis_of_basedSmoothLoopsBound`
and `smoothHurewiczHypothesis_of_wordRepresentative`, we also get
unconditional `WordRepresentativeHypothesis` and `SmoothHurewiczHypothesis`
on `X = ℂ` at the empty basis — extending the smooth-Hurewicz arc's
known-discharge coverage from `RiemannSphere` to a **second concrete
manifold** (the complex plane).

## What this file ships

* `basedSmoothLoopsBoundHypothesis_C_holds` — for any `p₀ : ℂ`, every
  smooth based loop at `p₀` is in `stokesBoundaries`.
* `wordRepresentativeHypothesis_emptyBasis_C_holds` — empty-basis
  word-rep on `ℂ`, unconditional.
* `smoothHurewiczHypothesis_C_emptyBasis_holds` — empty-basis
  smooth-Hurewicz on `ℂ`, unconditional.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

/-! ## Every based loop in ℂ is bordant to the constant loop -/

/-- **Every smooth based loop in `ℂ` at `p₀` is smoothly bordant to the
constant loop at `p₀`.** Direct specialization of
`smoothBordant_straightLineC` with `γ₁ := constBasedLoopAt p₀`. -/
theorem smoothBordant_to_const_C
    (p₀ : ℂ) (γ : BasedLoopAt 𝓘(ℝ, ℂ) ℂ p₀) :
    SmoothBordant γ (constBasedLoopAt p₀) :=
  smoothBordant_straightLineC γ (constBasedLoopAt p₀)

/-! ## `BasedSmoothLoopsBoundHypothesis` on `ℂ` -/

/-- **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) ℂ p₀`** holds
unconditionally for any `p₀ : ℂ`.

Proof: from `smoothBordant_to_const_C`, every based loop's
`singleCycle` differs from `(constBasedLoopAt p₀).singleCycle` by a
Stokes-boundary. Adding the const-singleCycle (itself in
stokesBoundaries) gives the loop's singleCycle ∈ stokesBoundaries. -/
theorem basedSmoothLoopsBoundHypothesis_C_holds (p₀ : ℂ) :
    BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) ℂ p₀ := by
  intro γ h_src h_tgt
  -- Package γ as a BasedLoopAt.
  let γ_bl : BasedLoopAt 𝓘(ℝ, ℂ) ℂ p₀ := ⟨γ, ⟨h_src, h_tgt⟩⟩
  -- (1) Bordism: γ_bl.singleCycle - constBasedLoopAt.singleCycle ∈ stokes.
  have h_bord : SmoothBordant γ_bl (constBasedLoopAt p₀) :=
    smoothBordant_to_const_C p₀ γ_bl
  -- (2) constBasedLoopAt.singleCycle = single_smoothPath_const_smoothCycle p₀.
  have h_const_eq := constBasedLoopAt_singleCycle p₀
  -- (3) single_smoothPath_const_smoothCycle p₀ ∈ stokes.
  have h_const_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ) p₀
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) ℂ :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  have h_constBL_in : (constBasedLoopAt p₀).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) ℂ := by
    rw [h_const_eq]; exact h_const_in
  -- (4) γ_bl.singleCycle = (γ_bl.singleCycle - constBL.singleCycle) + constBL.singleCycle ∈ stokes.
  have h_diff_in : γ_bl.singleCycle - (constBasedLoopAt p₀).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) ℂ := h_bord
  have h_sum : (γ_bl.singleCycle - (constBasedLoopAt p₀).singleCycle)
      + (constBasedLoopAt p₀).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) ℂ :=
    AddSubgroup.add_mem _ h_diff_in h_constBL_in
  -- (5) Show this equals γ_bl.singleCycle, then transport.
  have h_eq : (γ_bl.singleCycle - (constBasedLoopAt p₀).singleCycle)
      + (constBasedLoopAt p₀).singleCycle = γ_bl.singleCycle := by abel
  rw [h_eq] at h_sum
  -- (6) γ_bl.singleCycle = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm).
  have h_γ_sing :
      γ_bl.singleCycle
        = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) := by
    apply Subtype.ext
    rw [BasedLoopAt.singleCycle_coe, single_smoothLoop_smoothCycle_coe]
    rfl
  rw [h_γ_sing] at h_sum
  exact h_sum

/-! ## Downstream: empty-basis word-rep and smooth-Hurewicz on ℂ -/

/-- **Empty-basis `WordRepresentativeHypothesis` on `ℂ`, unconditional.**
Composes `wordRepresentativeHypothesis_emptyBasis_of_basedSmoothLoopsBound`
with `basedSmoothLoopsBoundHypothesis_C_holds`. -/
theorem wordRepresentativeHypothesis_emptyBasis_C_holds
    (p₀ : ℂ)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) ℂ p₀ 0) :
    WordRepresentativeHypothesis sb :=
  wordRepresentativeHypothesis_emptyBasis_of_basedSmoothLoopsBound p₀ sb
    (basedSmoothLoopsBoundHypothesis_C_holds p₀)

/-- **`SmoothHurewiczHypothesis` on `ℂ` at the empty basis,
unconditional.** End-to-end: straight-line homotopy → const-bordism →
based-loops bound → empty-basis word-rep → smooth-Hurewicz. -/
theorem smoothHurewiczHypothesis_C_emptyBasis_holds
    (p₀ : ℂ)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) ℂ p₀ 0) :
    SmoothHurewiczHypothesis sb :=
  smoothHurewiczHypothesis_of_wordRepresentative
    (wordRepresentativeHypothesis_emptyBasis_C_holds p₀ sb)

end JacobianChallenge

end
