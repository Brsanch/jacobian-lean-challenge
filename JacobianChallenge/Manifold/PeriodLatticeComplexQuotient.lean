/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.NormedSpace.Connected
import JacobianChallenge.Manifold.PeriodLatticeLieGroup

/-! # Complex-model `IsManifold 𝓘(ℂ, Fin g → ℂ) ω ((Fin g → ℂ) ⧸ Λ)`

Companion to `PeriodLatticeChartedSpace.lean` (charted space) and
`PeriodLatticeLieGroup.lean` (real-model `IsManifold`). For a `ℤ`-lattice
`Λ ≤ Fin g → ℂ` (viewed as a real `2g`-dimensional space) which is
`DiscreteTopology` and `IsZLattice ℝ`, the quotient
`(Fin g → ℂ) ⧸ Λ` carries the **complex-model** analytic manifold
structure modeled on `Fin g → ℂ`.

The `ChartedSpace (Fin g → ℂ) ((Fin g → ℂ) ⧸ Λ)` instance is identical
to the one supplied by `chartedSpace_quotient_of_zlattice` — it is purely
topological/set-level data and does not depend on the choice of scalar
field for the model with corners. The new content here is the
**complex-`ω`** chart-change regularity:

* Each chart-transition is, on a neighborhood of every point of its
  source, equal to a translation `x ↦ x - λ` for a fixed lattice element
  `λ ∈ Λ` (this is `transition_eventuallyEq_translation` from the
  real-model file).
* Translation by a constant on a `ℂ`-normed space is `ContDiff ℂ ω`
  (analytic), via `contDiff_id.sub contDiff_const`.

Hence the chart-transition is `ContDiff ℂ ω` on its source, and
`isManifold_of_contDiffOn` lifts this to the desired manifold instance.
-/

open Set Metric

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {g : ℕ}
variable (L : Submodule ℤ (Fin g → ℂ))
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ### Complex-`ω` chart-transition regularity -/

/-- Subtraction of a constant on a `ℂ`-normed space is `ContDiff ℂ n`. -/
private lemma contDiff_C_sub_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {n : WithTop ℕ∞} (c : E) :
    ContDiff ℂ n (fun x : E => x - c) :=
  contDiff_id.sub contDiff_const

/-- Chart-change between any two atlas elements is `ContDiff ℂ ω` on its
source, because it equals translation by a lattice element on a
neighborhood of every point and translation is complex-analytic. -/
private lemma contDiffOn_chart_transition_C
    {r : ℝ} (hrL : ∀ x ∈ (L : Set (Fin g → ℂ)), ‖x‖ < r → x = 0)
    (c c' : Fin g → ℂ) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n
      ((localChart L hrL c).trans (localChart L hrL c').symm)
      ((localChart L hrL c).trans (localChart L hrL c').symm).source := by
  intro x₀ hx₀
  obtain ⟨lam, _hlam_mem, h_eqOn⟩ :=
    transition_eventuallyEq_translation L hrL c c' hx₀
  have hCD : ContDiffWithinAt ℂ n (fun x : (Fin g → ℂ) => x - lam)
      (((localChart L hrL c).trans (localChart L hrL c').symm).source) x₀ :=
    (contDiff_C_sub_const lam).contDiffWithinAt
  exact hCD.congr_of_eventuallyEq (h_eqOn.filter_mono nhdsWithin_le_nhds)
      (h_eqOn.self_of_nhds)

/-! ### Complex-model `ChartedSpace` and `IsManifold` instances -/

/-- The quotient `(Fin g → ℂ) ⧸ Λ` of a complex coordinate space by a
discrete `ℤ`-lattice `Λ` (full-rank in the underlying real
`2g`-dimensional space) carries a `ChartedSpace (Fin g → ℂ)` structure.

This is identical, as a `ChartedSpace`, to the instance supplied by
`chartedSpace_quotient_of_zlattice`; we re-export it under a separate
`def`-style name for documentation. -/
noncomputable def complex_chartedSpace_quotient_of_zlattice :
    ChartedSpace (Fin g → ℂ) ((Fin g → ℂ) ⧸ L) :=
  chartedSpace_quotient_of_zlattice L

/-- **Complex-`ω` analytic manifold structure on `(Fin g → ℂ) ⧸ Λ`.**
For a discrete full-rank `ℤ`-lattice `Λ`, the quotient is an analytic
manifold modeled on `Fin g → ℂ` with the standard complex model
`𝓘(ℂ, Fin g → ℂ)`. The chart-changes are local translations by lattice
elements, which are complex-affine and thus `ContDiff ℂ ω`. -/
noncomputable def complex_isManifold_quotient_of_zlattice (n : WithTop ℕ∞) :
    @IsManifold ℂ _ (Fin g → ℂ) _ _ (Fin g → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin g → ℂ)) n
      ((Fin g → ℂ) ⧸ L) _ (chartedSpace_quotient_of_zlattice L) := by
  refine isManifold_of_contDiffOn 𝓘(ℂ, Fin g → ℂ) n ((Fin g → ℂ) ⧸ L) ?_
  intro e e' he he'
  rcases he with ⟨c, hce⟩
  rcases he' with ⟨c', hc'e'⟩
  subst hce
  subst hc'e'
  have h := contDiffOn_chart_transition_C L (discRadius_separates L) c c' n
  simp only [mfld_simps] at h ⊢
  exact h

/-- Instance form of `complex_isManifold_quotient_of_zlattice` at
analytic regularity (`n = ω`). Registered as an instance so that
downstream consumers — in particular the `PeriodLatticeOfRankTwoG`
bundle's `ChartedSpaceHypothesis` (item 5/12 of OPEN.md) — can pick it
up automatically. -/
noncomputable instance complex_isManifold_quotient_of_zlattice_omega :
    @IsManifold ℂ _ (Fin g → ℂ) _ _ (Fin g → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin g → ℂ)) ω
      ((Fin g → ℂ) ⧸ L) _ (chartedSpace_quotient_of_zlattice L) :=
  complex_isManifold_quotient_of_zlattice L ω

end JacobianChallenge
