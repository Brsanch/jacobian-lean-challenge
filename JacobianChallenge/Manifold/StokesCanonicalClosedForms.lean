/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.StokesBoundaryInvarianceFromSimplex
import JacobianChallenge.Manifold.SmoothPathIntegrability

set_option linter.unusedSectionVars false

/-! # Canonical Stokes-closed forms submodule and canonical `StokesBoundaryInvariance`

The previous `StokesBoundaryInvariance` bundle requires the consumer to
supply *both* a chosen `closedForms` submodule and a vanishing
hypothesis. With `Smooth2Chain.boundary₂Cycle` and `stokesBoundaries`
now canonical, we can canonically define:

* `canonicalClosedForms I X` — the submodule of real 1-forms whose
  integral around the boundary of **every** smooth 2-simplex vanishes
  (the largest submodule for which `IntegrationStokesHypothesis` holds).
* `canonicalIntegrationStokes I X` — the tautological discharge of
  `IntegrationStokesHypothesis` against `canonicalClosedForms`.
* `StokesBoundaryInvariance.canonical I X` — the canonical
  parameter-free `StokesBoundaryInvariance` bundle, with
  `boundaries = stokesBoundaries I X` and
  `closedForms = canonicalClosedForms I X`.

A 1-form `ω` lies in `canonicalClosedForms` iff it is "Stokes-closed"
in the most direct algebraic sense: `∫_{∂σ} ω = 0` for every smooth
2-simplex `σ`. This is the form-side companion of `stokesBoundaries`
being the cycle-side image of `∂₂`.

## Why this matters

This drops the user-visible interface of the period-lattice classical
input from **three** Stokes-side fields (boundaries, closedForms,
vanishing) to **zero**: the bundle is now canonical, and the user need
only supply the "every holomorphic form has Stokes-vanishing real and
imaginary parts" hypothesis on this canonical bundle (an actual
classical content statement, not a setup-of-the-bundle one).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## Canonical `closedForms` submodule -/

/-- **Canonical Stokes-closed forms.** The submodule of real
1-forms whose integral around the boundary of every smooth 2-simplex
vanishes. This is the largest submodule of `SmoothOneForm I X` against
which `IntegrationStokesHypothesis` is tautologically true; geometrically,
it is the algebraic closure of "closed" 1-forms accessible from the
single-simplex Stokes hypothesis alone. -/
def canonicalClosedForms (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    Submodule ℝ (SmoothOneForm I X) where
  carrier :=
    { om | ∀ σ : Smooth2Simplex I X,
        SmoothChain.integrate (Smooth2Simplex.boundary σ) om = 0 }
  zero_mem' := by
    intro σ
    exact smoothChain_realOneForm_pairing_zero_right (Smooth2Simplex.boundary σ)
  add_mem' := by
    intro om₁ om₂ h₁ h₂ σ
    rw [SmoothChain.integrate_add_form, h₁ σ, h₂ σ, add_zero]
  smul_mem' := by
    intro a om h σ
    rw [SmoothChain.integrate_smul_form, h σ, mul_zero]

@[simp] lemma mem_canonicalClosedForms_iff {om : SmoothOneForm I X} :
    om ∈ canonicalClosedForms I X
      ↔ ∀ σ : Smooth2Simplex I X,
          SmoothChain.integrate (Smooth2Simplex.boundary σ) om = 0 := Iff.rfl

/-- **Tautological discharge** of the single-simplex Stokes hypothesis
against the canonical closed-forms submodule. -/
theorem canonicalIntegrationStokes (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    IntegrationStokesHypothesis I X (canonicalClosedForms I X) := by
  intro σ om hom
  exact hom σ

/-! ## Canonical `StokesBoundaryInvariance` -/

/-- **Canonical `StokesBoundaryInvariance` bundle.** With
`boundaries := stokesBoundaries I X` (image of `∂₂`) and
`closedForms := canonicalClosedForms I X` (kernel of integrate-against-
∂σ for every σ), the vanishing hypothesis is *automatic* via
`ofSingleSimplexStokes` + `canonicalIntegrationStokes`. -/
noncomputable def StokesBoundaryInvariance.canonical
    (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    StokesBoundaryInvariance I X :=
  StokesBoundaryInvariance.ofSingleSimplexStokes
    (canonicalClosedForms I X) (canonicalIntegrationStokes I X)

@[simp] lemma StokesBoundaryInvariance.canonical_boundaries
    (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    (StokesBoundaryInvariance.canonical I X).boundaries
      = stokesBoundaries I X := rfl

@[simp] lemma StokesBoundaryInvariance.canonical_closedForms
    (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    (StokesBoundaryInvariance.canonical I X).closedForms
      = canonicalClosedForms I X := rfl

end JacobianChallenge

end
