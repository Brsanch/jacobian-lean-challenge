/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneBijective
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphism
import JacobianChallenge.Manifold.HolomorphicEquivDegreeFiber
import JacobianChallenge.Topology.UniformizationFromRiemannRoch
import JacobianChallenge.Topology.Item14FromSingleUniformization

set_option diagnostics.threshold 100

/-! # Item 14 final closure composition

This file ships the **final composition** of all named conditional
hypotheses landed across zz309–zz330 into a single theorem stating
how item 14 closes from explicit classical inputs.

## Current state (2026-05-26) — only inputs 4 + 5 remain open

Inputs 1, 2, 3 below are **unconditionally discharged in tree**.
The theorem `degreeOneIsBiholomorphic_RS_of_conditionals` below
still takes them as hypotheses for compositional clarity, but they
are now consumed at the call sites via the named `_holds*` /
`_holds_unconditional` theorems. See
`Topology/HTopFromSubsingleton.lean:101-107` for the unconditional
call-site composition, and `HANDOFF_ITEM14.md` "ACTIVE ARC —
CANONICAL CURRENT STATE" for the single-theorem frontier.

The genuinely-open inputs are 4 (`RiemannRochGenusZero X`, =
Forster Thm 16.9 by 1-input reduction in
`Topology/RiemannRochGenusZeroSingleInput.lean`) and 5 (the
topological-sphere half of uniformization).

## The five named inputs (with current status)

  1. `ramificationSumEqualsDegree_statement X RS` — sum of ram
     indices over a fibre equals the degree.
     **UNCONDITIONAL** via
     `Manifold/RamificationSumEqualsDegreeUnconditional.lean:471`
     composed with `Manifold/NearbyRegularWitnessHolds.lean:32`.

  2. `Surjective_of_NonConstant_Analytic_Manifold X RS` — non-constant
     ω-smooth maps are surjective. **UNCONDITIONAL** via
     `Manifold/SurjectiveOfNonConstantDischarge.lean:391`.

  3. `BijectiveAnalyticIsBiholomorphism X` — bijective ω-smooth maps
     upgrade to biholomorphisms. **UNCONDITIONAL** via
     `Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`.

  4. `RiemannRochGenusZero X` — Riemann-Roch produces a degree-1
     meromorphic function on genus-0 surfaces. **OPEN.** Reduces to
     `ExistsMeroSimplePole_GenusZero X` (Forster Thm 16.9) via
     `Topology/RiemannRochGenusZeroSingleInput.lean:54`. Equivalent
     to four other classical statements per HANDOFF canonical.

Plus the topological-sphere half of `UniformizationToRiemannSphere`:

  5. `Nonempty (X ≃ₜ StandardS2) → Nonempty (HolomorphicEquiv X RS)` —
     uniformization for topological spheres. **OPEN.** Equivalent
     to (4) via Dolbeault / Hodge / Serre / uniformization
     classical equivalences.

## What ships here

* `degreeOneIsBiholomorphic_RS_of_conditionals` — chains conditionals
  1, 2, 3 to close zz325's `DegreeOneIsBiholomorphic_RS X`.
* `uniformizationToRiemannSphere_of_all_conditionals` — chains
  conditionals 1, 2, 3, 4, 5 to close zz309's
  `UniformizationToRiemannSphere X`.
* `genus_eq_zero_iff_homeo_from_all_conditionals` — the headline
  biconditional of item 14 from the five named classical inputs.

This is the maximally-compressed closure chain at the current pin:
five named classical theorems (none in mathlib), all explicit, all
referenced to standard textbooks. The Lean composition is mechanical.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`DegreeOneIsBiholomorphic_RS X` from three named conditionals.** -/
theorem degreeOneIsBiholomorphic_RS_of_conditionals
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement
      X JacobianChallenge.RiemannSphere)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold
      X JacobianChallenge.RiemannSphere)
    (h_bij : BijectiveAnalyticIsBiholomorphism.{u, 0} X) :
    DegreeOneIsBiholomorphic_RS X := by
  intro f hf hnc h_deg
  have hbij : Function.Bijective f :=
    bijective_of_degreeFiber_eq_one h_RS h_surj hf hnc h_deg
  exact h_bij f hf hbij

/-- **`UniformizationToRiemannSphere X` from all named conditionals.** -/
theorem uniformizationToRiemannSphere_of_all_conditionals
    (hRR : RiemannRochGenusZero X)
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement
      X JacobianChallenge.RiemannSphere)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold
      X JacobianChallenge.RiemannSphere)
    (h_bij : BijectiveAnalyticIsBiholomorphism.{u, 0} X)
    (h_top : Nonempty (X ≃ₜ StandardS2) →
      Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)) :
    UniformizationToRiemannSphere X := by
  intro h
  rcases h with hg | hHomeo
  · -- genus X = 0 branch: use Riemann-Roch + degree-1-is-biholomorphism.
    exact uniformizationToRiemannSphere_genus_zero_branch_from_RR X hRR
      (degreeOneIsBiholomorphic_RS_of_conditionals h_RS h_surj h_bij) hg
  · -- topological-sphere branch: use uniformization-for-spheres.
    exact h_top hHomeo

/-- **Item 14 biconditional from all named conditionals.** -/
theorem genus_eq_zero_iff_homeo_from_all_conditionals
    (hRR : RiemannRochGenusZero X)
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement
      X JacobianChallenge.RiemannSphere)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold
      X JacobianChallenge.RiemannSphere)
    (h_bij : BijectiveAnalyticIsBiholomorphism.{u, 0} X)
    (h_top : Nonempty (X ≃ₜ StandardS2) →
      Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere
    (uniformizationToRiemannSphere_of_all_conditionals hRR h_RS h_surj h_bij h_top)

end JacobianChallenge

end
