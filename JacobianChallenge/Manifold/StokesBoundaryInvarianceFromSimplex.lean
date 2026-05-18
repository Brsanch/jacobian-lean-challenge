/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2ChainStokesBoundary
import JacobianChallenge.Manifold.H1SmoothMod
import JacobianChallenge.Manifold.SmoothChainIntegralLinearity

set_option linter.unusedSectionVars false

/-! # Honest `StokesBoundaryInvariance` from a single-simplex Stokes hypothesis

`H1SmoothMod.StokesBoundaryInvariance` packages three fields. The
legacy file leaves all three as named hypotheses; this file collapses
the first slot **canonically**: `boundaries` becomes
`stokesBoundaries I X` (the image of `Smooth2Chain.boundary₂Cycle`)
from `Smooth2ChainStokesBoundary.lean`, and the vanishing field is
discharged from a **single-simplex Stokes hypothesis**.

That hypothesis is the **only** remaining classical content: the
genuine content of Stokes' theorem on smooth 2-simplices
(`∫_{∂σ} ω = ∫∫_σ dω`, with the RHS vanishing for closed `ω`).

## Net contribution

* `IntegrationStokesHypothesis I X closedForms` — the named
  single-simplex Stokes content (a `Prop`).
* `StokesBoundaryInvariance.ofSingleSimplexStokes` — honest
  constructor: `boundaries := stokesBoundaries`, vanishing
  discharged from the named `Prop` via the additivity of
  `SmoothChain.integrate`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **Single-simplex Stokes hypothesis.** For each smooth 2-simplex
`σ` and each "closed" 1-form `ω ∈ closedForms`, the integral of `ω`
around the boundary `∂σ = face₀ - face₁ + face₂` vanishes. -/
def IntegrationStokesHypothesis
    (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (closedForms : Submodule ℝ (SmoothOneForm I X)) : Prop :=
  ∀ σ : Smooth2Simplex I X, ∀ oneForm ∈ closedForms,
    SmoothChain.integrate (Smooth2Simplex.boundary σ) oneForm = 0

namespace IntegrationStokesHypothesis

variable {closedForms : Submodule ℝ (SmoothOneForm I X)}

/-- **Extension to 2-chains by linearity.** -/
theorem integrate_boundary₂_eq_zero
    (h : IntegrationStokesHypothesis I X closedForms)
    (c : Smooth2Chain I X) {oneForm : SmoothOneForm I X}
    (hClosed : oneForm ∈ closedForms) :
    SmoothChain.integrate (Smooth2Chain.boundary₂ c) oneForm = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
    have h_z : (Smooth2Chain.boundary₂ : Smooth2Chain I X →ₗ[ℤ] _) 0 = 0 := map_zero _
    show SmoothChain.integrate (Smooth2Chain.boundary₂ 0) oneForm = 0
    rw [h_z, SmoothChain.integrate_zero]
  | add c₁ c₂ ih₁ ih₂ =>
    have h_a : (Smooth2Chain.boundary₂ : Smooth2Chain I X →ₗ[ℤ] _) (c₁ + c₂)
        = Smooth2Chain.boundary₂ c₁ + Smooth2Chain.boundary₂ c₂ := map_add _ _ _
    show SmoothChain.integrate (Smooth2Chain.boundary₂ (c₁ + c₂)) oneForm = 0
    rw [h_a, SmoothChain.integrate_add, ih₁, ih₂, add_zero]
  | single σ k =>
    -- `Finsupp.single σ k = k • single σ`.
    have h_single_eq :
        (Finsupp.single σ k : Smooth2Chain I X) = k • Smooth2Chain.single σ := by
      show Finsupp.single σ k = k • Finsupp.single σ (1 : ℤ)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have h_smul : (Smooth2Chain.boundary₂ : Smooth2Chain I X →ₗ[ℤ] _)
        (k • Smooth2Chain.single σ)
        = k • Smooth2Chain.boundary₂ (Smooth2Chain.single σ) := map_smul _ _ _
    show SmoothChain.integrate (Smooth2Chain.boundary₂ (Finsupp.single σ k)) oneForm = 0
    rw [h_single_eq, h_smul, Smooth2Chain.boundary₂_single]
    rw [SmoothChain.integrate_zsmul, h σ oneForm hClosed, smul_zero]

end IntegrationStokesHypothesis

/-- **Honest `StokesBoundaryInvariance` from the single-simplex
Stokes hypothesis.** -/
noncomputable def StokesBoundaryInvariance.ofSingleSimplexStokes
    (closedForms : Submodule ℝ (SmoothOneForm I X))
    (h : IntegrationStokesHypothesis I X closedForms) :
    StokesBoundaryInvariance I X where
  boundaries := stokesBoundaries I X
  closedForms := closedForms
  pairing_vanishes_on_boundaries := by
    intro c hc oneForm hClosed
    rcases (mem_stokesBoundaries_iff (I := I) (X := X)).mp hc with ⟨d, hd⟩
    show SmoothCycle.integrate c oneForm = 0
    rw [SmoothCycle.integrate_eq]
    have h_coe_eq : (c : SmoothChain I X) = Smooth2Chain.boundary₂ d := by
      rw [← hd]
      exact Smooth2Chain.boundary₂Cycle_coe d
    rw [h_coe_eq]
    exact IntegrationStokesHypothesis.integrate_boundary₂_eq_zero h d hClosed

@[simp] lemma StokesBoundaryInvariance.ofSingleSimplexStokes_boundaries
    (closedForms : Submodule ℝ (SmoothOneForm I X))
    (h : IntegrationStokesHypothesis I X closedForms) :
    (StokesBoundaryInvariance.ofSingleSimplexStokes closedForms h).boundaries
      = stokesBoundaries I X := rfl

@[simp] lemma StokesBoundaryInvariance.ofSingleSimplexStokes_closedForms
    (closedForms : Submodule ℝ (SmoothOneForm I X))
    (h : IntegrationStokesHypothesis I X closedForms) :
    (StokesBoundaryInvariance.ofSingleSimplexStokes closedForms h).closedForms
      = closedForms := rfl

end JacobianChallenge

end
