/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesH1Generation

set_option linter.unusedSectionVars false

/-! # Trivial-at-genus-zero inhabitant of `C3PeriodLatticeStokesSpanTopInputs`

The refactored period-lattice classical inputs of
`C3PeriodLatticeStokesSpanTopInputs basis` (Stokes bundle + H₁ ℤ-span)
are trivially constructible at `genus X = 0`, mirroring
`PeriodLatticeSymplecticBundle.trivial_at_genus_zero` on the
unrefactored bundle.

Required external hypothesis: `Subsingleton (HolomorphicOneForm X)`.
On a compact connected complex 1-manifold this is the genus-0
consequence of `holomorphicOneFormFiniteDim_holds` (item 1, unconditional
in tree), but we surface it as a free typeclass argument so the chip
stays decoupled from the item-14 path.

## The trivial inhabitant

* `cycleGens : Fin 0 → ...` — empty (after rewriting `2 * 0 = 0`).
* `riemannBilinear` — `linearIndependent_empty_type`.
* `stokes` — pick `boundaries := ⊤` and `closedForms := ⊥`. The
  vanishing field is vacuous because the only "closed" real 1-form
  is `0`, against which every cycle integrates to `0`.
* `holomorphic_closed` — every holomorphic 1-form is `0` (subsingleton),
  hence has zero real and imaginary components, hence lies in
  `closedHolomorphicForms = ⊥`.
* `H1_spans_top` — `S.H1 = SmoothCycle / ⊤` is subsingleton (only
  element is `0`), so `Submodule.span ℤ ∅ = ⊥ = ⊤` automatically.

This shows the refactored bundle flows through genus 0 unconditionally
modulo a single subsingleton hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Auxiliary: subsingleton instance on the H₁ quotient by ⊤ -/

/-- The quotient of an additive group by the top subgroup is
subsingleton (everything collapses to a single class). -/
private lemma subsingleton_quotientAddGroup_top
    (G : Type*) [AddGroup G] :
    Subsingleton (G ⧸ (⊤ : AddSubgroup G)) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂' a b ?_
  intro c₁ c₂
  -- `QuotientAddGroup.mk c₁ = QuotientAddGroup.mk c₂` iff `c₁ - c₂ ∈ ⊤`.
  refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
  exact AddSubgroup.mem_top _

/-! ## The trivial inhabitant -/

/-- **Trivial inhabitant at genus 0.** Given `Subsingleton
(HolomorphicOneForm X)` (the genus-0 consequence of finite-dimensionality,
i.e. item 1 unconditional), the refactored period-lattice classical
inputs are constructible without analytic content. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero
    [Subsingleton (HolomorphicOneForm X)]
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    C3PeriodLatticeStokesSpanTopInputs basis := by
  -- Build the Stokes bundle: boundaries := ⊤, closedForms := ⊥.
  let stokes : StokesBoundaryInvariance 𝓘(ℝ, ℂ) X :=
    { boundaries := (⊤ : AddSubgroup (SmoothCycle 𝓘(ℝ, ℂ) X))
      closedForms := (⊥ : Submodule ℝ (SmoothOneForm 𝓘(ℝ, ℂ) X))
      pairing_vanishes_on_boundaries := by
        intro c _ om hom
        -- om ∈ ⊥ ↔ om = 0; integrating against 0 is 0.
        have hom0 : om = 0 := (Submodule.mem_bot ℝ).mp hom
        rw [hom0]
        exact SmoothCycle.integrate_zero_right c }
  -- Subsingleton on stokes.H1 = SmoothCycle / ⊤.
  haveI hsub_H1 : Subsingleton stokes.H1 :=
    subsingleton_quotientAddGroup_top _
  refine
    { cycleGens := ?_
      riemannBilinear := ?_
      stokes := stokes
      holomorphic_closed := ?_
      H1_spans_top := ?_ }
  · -- cycleGens : Fin (2 * 0) → ... — use Fin.elim0 after rewriting.
    rw [hgenus, Nat.mul_zero]
    exact Fin.elim0
  · -- riemannBilinear: ℝ-LI over Fin 0 of any function is trivial.
    -- After rewriting genus to 0, the domain becomes Fin 0.
    -- LinearIndependent on Fin 0 → V is vacuously true via
    -- `linearIndependent_empty_type` once we have IsEmpty (Fin 0).
    have hempty : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
      rw [hgenus, Nat.mul_zero]; infer_instance
    exact linearIndependent_empty_type
  · -- holomorphic_closed: every om ∈ closedHolomorphicForms stokes.
    -- closedHolomorphicForms := {om | realComponent om ∈ ⊥ ∧ imagComponent om ∈ ⊥}.
    -- With om = 0 (Subsingleton), realComponent 0 = 0 ∈ ⊥, imagComponent 0 = 0 ∈ ⊥.
    intro om
    have hom0 : om = 0 := Subsingleton.elim _ _
    rw [hom0]
    exact stokes.closedHolomorphicForms.zero_mem
  · -- H1_spans_top: span ℤ ∅ = ⊤ in a subsingleton group.
    -- LHS = Submodule.span ℤ ∅ = ⊥. RHS = ⊤. Both equal in a
    -- subsingleton group (`Subsingleton.elim`).
    exact Subsingleton.elim _ _

end JacobianChallenge

end
