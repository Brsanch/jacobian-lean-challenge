/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FDerivRestrictScalarsComplexIdentity
import JacobianChallenge.Manifold.RestrictScalarsContinuityComplex
import JacobianChallenge.Manifold.LocalCoeffDifferentiableOnReal
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option linter.unusedSectionVars false

/-! # `ContDiffOn ℂ ⊤ f S → ContDiffOn ℝ 1 f S` for `f : ℂ → ℂ` on open `S`

Builds on the hand-rolled `HasFDerivAt` bridge (chip 5,
`HasFDerivAtRestrictScalarsComplex.lean`), the `fderiv` identity
(chip 6, `FDerivRestrictScalarsComplexIdentity.lean`), and the
hand-rolled function-level continuity of `restrictScalars` (chip 8,
`RestrictScalarsContinuityComplex.lean`).

Uses mathlib's `contDiffOn_succ_iff_fderivWithin` characterization at
`n = 0`:
  `ContDiffOn ℝ 1 f S ↔ DifferentiableOn ℝ f S
    ∧ (0 = ω → AnalyticOn ℝ f S)
    ∧ ContDiffOn ℝ 0 (fderivWithin ℝ f S) S`
(the `0 = ω` clause is vacuous; `ContDiffOn ℝ 0` is `ContinuousOn`).

Both ingredients follow from the bridge chain:
* `DifferentiableOn ℝ f S` ← `DifferentiableOn.restrictScalarsComplex`.
* `ContinuousOn (fderivWithin ℝ f S) S` ← `fderivWithin` identity
  pulls back to `ContinuousOn ((·.restrictScalars ℝ) ∘ fderivWithin ℂ f S) S`,
  closed by `continuous_restrictScalars_complex.comp_continuousOn` +
  `ContDiffOn.continuousOn_fderivWithin` (ℂ-side, from `ContDiffOn ℂ 1`).

## What this file ships

* `ContDiffOn.complex_top_to_real_one` — the abstract bridge:
  `ContDiffOn ℂ ⊤ f S` on open `S` → `ContDiffOn ℝ 1 f S` for
  `f : ℂ → ℂ`.
* `HolomorphicOneForm.localCoeff_contDiffOn_real_one` — concrete
  specialization for `localCoeff om y` on `(chartAt ℂ y).target`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology ContDiff

/-- **Abstract `ContDiffOn ℝ 1`-bridge** for `f : ℂ → ℂ` on open `S`. -/
theorem ContDiffOn.complex_top_to_real_one
    {f : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S) (h : ContDiffOn ℂ ⊤ f S) :
    ContDiffOn ℝ 1 f S := by
  have hUD : UniqueDiffOn ℝ S := hS.uniqueDiffOn
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 from rfl,
      contDiffOn_succ_iff_fderivWithin hUD]
  have h_diff_R : DifferentiableOn ℝ f S := by
    have h_diff_C : DifferentiableOn ℂ f S := h.differentiableOn (by decide)
    exact h_diff_C.restrictScalarsComplex
  refine ⟨h_diff_R, ?_, ?_⟩
  · intro h_eq; exact absurd h_eq (by decide)
  · rw [contDiffOn_zero]
    have h_eq : Set.EqOn (fderivWithin ℝ f S)
        (fun x => (fderivWithin ℂ f S x).restrictScalars ℝ) S := by
      intro x hx
      have h_diff_C : DifferentiableWithinAt ℂ f S x :=
        (h x hx).differentiableWithinAt (by decide)
      have h_uniq : UniqueDiffWithinAt ℝ S x := hUD x hx
      exact fderivWithin_real_eq_fderivWithin_complex_restrictScalars h_diff_C h_uniq
    refine ContinuousOn.congr ?_ h_eq
    have hUD_C : UniqueDiffOn ℂ S := hS.uniqueDiffOn
    have h_fderiv_C : ContinuousOn (fderivWithin ℂ f S) S := by
      have h1 : ContDiffOn ℂ 1 f S := h.of_le le_top
      exact h1.continuousOn_fderivWithin hUD_C le_rfl
    exact continuous_restrictScalars_complex.comp_continuousOn h_fderiv_C

open scoped Manifold

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **`ContDiffOn ℝ 1`-form of `localCoeff_contMDiffOn` on the chart target.**

Concrete specialization of `ContDiffOn.complex_top_to_real_one` applied
to `localCoeff om y` on the (open) chart target `(chartAt ℂ y).target`. -/
theorem localCoeff_contDiffOn_real_one (om : HolomorphicOneForm X) (y : X) :
    ContDiffOn ℝ 1 (localCoeff om y) (chartAt ℂ y).target := by
  have h_C : ContDiffOn ℂ ⊤ (localCoeff om y) (chartAt ℂ y).target :=
    (localCoeff_contMDiffOn om y).contDiffOn
  exact ContDiffOn.complex_top_to_real_one (chartAt ℂ y).open_target h_C

end HolomorphicOneForm

end
