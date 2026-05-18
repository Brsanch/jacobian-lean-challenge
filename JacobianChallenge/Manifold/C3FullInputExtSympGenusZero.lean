/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Pic0RiemannSphereSymp
import JacobianChallenge.Manifold.SmoothPathConnectedRiemannSphereSymp
import JacobianChallenge.Manifold.JacobianAnalyticChoiceSymp
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Genus-0 / RiemannSphere discharges of the extended C3 inputs

Composes the prior genus-0 / RS chips into:

1. **Smoothness at genus 0**: `AbelJacobiSmoothnessSymp B` for any
   `B : AbelJacobiInputSymp α h` whenever `genus X = 0`. Trivial via
   subsingleton codomain — `B.abelJacobiPoint` is a function into a
   one-point space, hence constant, hence `ContMDiff`.

2. **Injectivity at genus 0**: `AbelJacobiInjectiveSymp B` is the
   predicate `0 < genus X → Function.Injective …`. At `genus X = 0`
   the hypothesis is false, so the predicate is vacuously true.

3. **`C3FullInputExtSymp X` at genus 0**: Combines (1) + (2) with the
   prior `abelJacobiEquiv_of_genus_zero` discharges to build the full
   extended bundle at genus 0, modulo the named hypothesis
   `Subsingleton (Pic0 X)` (the genus-0 case of Abel's converse).

4. **`Nonempty (C3FullInputExtSymp RiemannSphere)` unconditional
   instance**: For `X = RiemannSphere`, `genus = 0` is unconditional
   (`genus_RiemannSphere_eq_zero`), `Subsingleton (Pic0 RS)` is
   unconditional (`subsingleton_pic0_RiemannSphere`), and an
   `AbelJacobiInputSymp` bundle exists unconditionally
   (`nonempty_abelJacobiInputSymp_RiemannSphere`). Discreteness bundle
   is `PeriodLatticeSymplecticBundle.trivial_at_genus_zero`.

The headline: `JacobianAnalyticChoiceSymp RiemannSphere` becomes
**unconditional** in tree, and `picZeroEquivSymp : Pic⁰ RS ≃+
JacobianAnalyticChoiceSymp RS` is the unconditional bridge for
Basic.lean's `Jacobian RiemannSphere`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Genus-0 discharge of `AbelJacobiSmoothnessSymp` -/

namespace AbelJacobiInputSymp

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Genus-zero discharge of `AbelJacobiSmoothnessSymp`.** At genus 0,
the analytic Jacobian is subsingleton (single point), so any function
into it is constant. Constant functions are `ContMDiff`. -/
theorem abelJacobiSmoothness_of_genus_zero
    (B : AbelJacobiInputSymp α h)
    (hgenus : JacobianChallenge.genus X = 0) :
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
    AbelJacobiSmoothnessSymp B := by
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
  -- Codomain is subsingleton at genus 0.
  haveI hsub : Subsingleton
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h) :=
    Subsingleton.analyticJacobianSymp_of_genus_zero
      (data := PeriodPairingData.ofSmoothCycle X) (α := α) (h := h) hgenus
  -- The predicate `AbelJacobiSmoothnessSymp B` unfolds (via its
  -- internal `haveI`) to a `ContMDiff` statement on
  -- `B.abelJacobiPoint : X → AnalyticJacobianSymp _ α h`. Construct that
  -- `ContMDiff` directly by exploiting that the function is constant
  -- (since the codomain is subsingleton at genus 0).
  suffices h : ∀ (_ : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h)),
      ContMDiff (𝓘(ℂ, ℂ))
        (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
        (B.abelJacobiPoint :
          X → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h) by
    exact h _
  intro _inst
  have h_const : (B.abelJacobiPoint :
      X → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h)
        = fun _ => (0 : AnalyticJacobianSymp _ α h) := by
    funext x
    exact Subsingleton.elim _ _
  rw [h_const]
  exact contMDiff_const

/-- **Genus-zero discharge of `AbelJacobiInjectiveSymp`.** Vacuous —
the hypothesis `0 < genus X` is false at genus 0. -/
theorem abelJacobiInjective_of_genus_zero
    (B : AbelJacobiInputSymp α h)
    (hgenus : JacobianChallenge.genus X = 0) :
    AbelJacobiInjectiveSymp B := by
  intro hpos
  rw [hgenus] at hpos
  exact absurd hpos (lt_irrefl 0)

end AbelJacobiInputSymp

/-! ## `C3FullInputExtSymp X` builder at genus 0 -/

/-- **Genus-zero composite — full `C3FullInputExtSymp` bundle from a
discreteness bundle, an AJ input, and `Subsingleton (Pic0 X)`.** -/
noncomputable def C3FullInputExtSymp.ofGenusZero
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInputSymp α h)
    (hgenus : JacobianChallenge.genus X = 0)
    (hPic0 : Subsingleton (Pic0 X)) :
    C3FullInputExtSymp X where
  base :=
    { basis := α
      discreteness := h
      ajInput := B
      abel := B.abelHypothesis_of_genus_zero hgenus
      jacobi := AbelJacobiInputSymp.jacobiInversion_of_genus_zero_and_subsingleton_pic0
        B (B.abelHypothesis_of_genus_zero hgenus) hgenus hPic0 }
  smoothness := B.abelJacobiSmoothness_of_genus_zero hgenus
  injective := B.abelJacobiInjective_of_genus_zero hgenus

/-! ## Unconditional `Nonempty (C3FullInputExtSymp RiemannSphere)` -/

/-- **`Nonempty (C3FullInputExtSymp RiemannSphere)` is unconditional.**
Composes:
* `genus_RiemannSphere_eq_zero` (unconditional in tree).
* `subsingleton_pic0_RiemannSphere` (unconditional in tree).
* `nonempty_abelJacobiInputSymp_RiemannSphere` (unconditional in tree
  via `smoothPathConnected_RiemannSphere`).
* `PeriodLatticeSymplecticBundle.trivial_at_genus_zero` (unconditional
  at genus 0 — empty tuple, empty basis, vacuous spanning condition). -/
instance nonempty_C3FullInputExtSymp_RiemannSphere :
    Nonempty (C3FullInputExtSymp RiemannSphere) := by
  classical
  -- Pick the canonical basis (empty, at genus 0).
  let α : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere) :=
    Module.finBasis ℂ _
  -- Build the trivial symplectic bundle at genus 0.
  let h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) α :=
    PeriodLatticeSymplecticBundle.trivial_at_genus_zero
      (data := PeriodPairingData.ofSmoothCycle RiemannSphere) (α := α)
      JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero
  -- Get an `AbelJacobiInputSymp` unconditionally.
  obtain ⟨B⟩ := nonempty_abelJacobiInputSymp_RiemannSphere α h
  -- Assemble via the genus-0 builder.
  exact ⟨C3FullInputExtSymp.ofGenusZero α h B
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero
    subsingleton_pic0_RiemannSphere⟩

end JacobianChallenge

end
