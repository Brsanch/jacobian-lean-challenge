/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobiInversionSurjectiveComplexTorus
import JacobianChallenge.Manifold.C3FullInputExtSympComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Injectivity of `abelJacobi : Pic⁰ T_L → AnalyticJacobianSymp`
reduced to **Abel's converse** at the T_L level

The injective half of `JacobiInversion` reduces, via the iso
`AnalyticJacobianSymp ≃+ T_L`, to the classical **Abel's converse**:
every degree-0 divisor on `T_L` whose support-weighted sum is `0` in
`T_L` is principal.

We name this hypothesis `TLAbelConverseHypothesis L` and show it
discharges `JacobiInversion.injective`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Named T_L-level Abel's-converse hypothesis -/

/-- **Abel's converse on `T_L`, as a named hypothesis.**

States: every degree-zero divisor `D : Div0 (ℂ⧸L)` whose
support-weighted sum vanishes in `T_L` is principal.

Classically: the existence of a meromorphic function with prescribed
zeros and poles, via the Weierstrass σ-function construction. -/
def TLAbelConverseHypothesis : Prop :=
  ∀ D : Div0 (ℂ ⧸ L),
    (∑ x ∈ ((D : Div (ℂ ⧸ L))).supportFinset,
      ((D : Div (ℂ ⧸ L)) : (ℂ ⧸ L) → ℤ) x • x : ℂ ⧸ L) = 0
    → (D : Div (ℂ ⧸ L)) ∈ PrincDiv (ℂ ⧸ L)

/-! ## Reduction: TLAbelConverseHypothesis ⟹ JacobiInversion.injective -/

/-- **The sum `∑ x, D x • x` in `T_L` equals `iso (abelJacobiDivHom D)`.**

This is the analytic centerpiece: under the iso
`AnalyticJacobianSymp ≃+ T_L`, the AJ image of any divisor is its
support-weighted sum in T_L. -/
theorem analyticJacobianSympEquiv_abelJacobiDivHom
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (D : Div (ℂ ⧸ L)) :
    analyticJacobianSympEquiv_complexTorus L h
        ((canonicalAbelJacobiInputSymp L h).abelJacobiDivHom D)
      = ∑ x ∈ D.supportFinset, (D : (ℂ ⧸ L) → ℤ) x • x := by
  show analyticJacobianSympEquiv_complexTorus L h
      (∑ x ∈ D.supportFinset,
        ((D : (ℂ ⧸ L) → ℤ) x) •
          (canonicalAbelJacobiInputSymp L h).abelJacobiPoint x) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [map_zsmul, analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]

/-- **`JacobiInversion.injective` from `TLAbelConverseHypothesis`.** -/
theorem jacobiInversion_injective_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Function.Injective
      ((canonicalAbelJacobiInputSymp L h).abelJacobi
        (abelHypothesis_complexTorus_of_TLDivSum L h hTL)) := by
  classical
  -- Standard reduction: injective ↔ ker = 0.
  rw [injective_iff_map_eq_zero (canonicalAbelJacobiInputSymp L h |>.abelJacobi
    (abelHypothesis_complexTorus_of_TLDivSum L h hTL))]
  intro c hc
  -- c : Pic⁰ T_L with abelJacobi hAbel c = 0. Need c = 0.
  induction c using QuotientAddGroup.induction_on with
  | H D₀ =>
  -- hc : abelJacobi hAbel (mk D₀) = 0.
  -- Convert: abelJacobiDiv (D₀ : Div) = 0.
  rw [AbelJacobiInputSymp.abelJacobi_mk_eq_abelJacobiDiv] at hc
  set hD_ker := hc
  -- hD_ker : abelJacobiDiv (D₀ : Div) = 0.
  -- Apply iso to both sides: iso 0 = 0; iso (abelJacobiDiv ...) = sum in T_L.
  have h_sum_zero :
      ∑ x ∈ ((D₀ : Div (ℂ ⧸ L))).supportFinset,
        ((D₀ : Div (ℂ ⧸ L)) : (ℂ ⧸ L) → ℤ) x • x = (0 : ℂ ⧸ L) := by
    have h_iso :=
      analyticJacobianSympEquiv_abelJacobiDivHom L h (D₀ : Div (ℂ ⧸ L))
    -- h_iso : iso (abelJacobiDivHom (D₀ : Div)) = ∑ x, D x • x
    show ∑ x ∈ ((D₀ : Div (ℂ ⧸ L))).supportFinset, _ • x = _
    rw [← h_iso]
    -- Now: iso (abelJacobiDivHom (D₀ : Div)) = 0.
    -- We have hD_ker : abelJacobiDiv (D₀ : Div) = 0. And abelJacobiDiv =
    -- abelJacobiDivHom in body.
    show analyticJacobianSympEquiv_complexTorus L h
        ((canonicalAbelJacobiInputSymp L h).abelJacobiDivHom
          (D₀ : Div (ℂ ⧸ L))) = 0
    have h_eq : (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom
        (D₀ : Div (ℂ ⧸ L))
        = (canonicalAbelJacobiInputSymp L h).abelJacobiDiv
          (D₀ : Div (ℂ ⧸ L)) := rfl
    rw [h_eq, hD_ker]
    exact (analyticJacobianSympEquiv_complexTorus L h).map_zero
  -- By hConverse, (D₀ : Div) ∈ PrincDiv.
  have h_princ : (D₀ : Div (ℂ ⧸ L)) ∈ PrincDiv (ℂ ⧸ L) :=
    hConverse D₀ h_sum_zero
  -- Hence mk D₀ = 0 in Pic⁰ = Div0 ⧸ (PrincDiv).addSubgroupOf Div0.
  show (QuotientAddGroup.mk D₀ : Pic0 (ℂ ⧸ L)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  -- Goal: D₀ ∈ (PrincDiv (ℂ⧸L)).addSubgroupOf (Div0 (ℂ⧸L))
  -- = {d : Div0 | (d : Div) ∈ PrincDiv}.
  exact h_princ

/-! ## Final headline: full `JacobiInversion` from two named hypotheses -/

/-- **Full `JacobiInversion` from `TLDivSumHypothesis` + `TLAbelConverseHypothesis`.** -/
theorem jacobiInversion_complexTorus_of_TLDivSum_and_TLAbelConverse
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    AbelJacobiInputSymp.JacobiInversion
      (canonicalAbelJacobiInputSymp L h)
      (abelHypothesis_complexTorus_of_TLDivSum L h hTL) :=
  { injective :=
      jacobiInversion_injective_complexTorus L h hTL hConverse
    surjective :=
      jacobiInversion_surjective_complexTorus L h
        (abelHypothesis_complexTorus_of_TLDivSum L h hTL) }

/-- **Full closure of the challenge for T_L from two named hypotheses.**

`Nonempty (C3FullInputExtSymp (ℂ⧸L))` from:
* `TLDivSumHypothesis L` — Abel's theorem on elliptic functions.
* `TLAbelConverseHypothesis L` — Weierstrass σ-function existence. -/
theorem nonempty_C3FullInputExtSymp_complexTorus_of_two_named_hypotheses
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Nonempty (JacobianChallenge.C3FullInputExtSymp (ℂ ⧸ L)) :=
  nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum_and_jacobiInversion L h
    hTL
    (jacobiInversion_complexTorus_of_TLDivSum_and_TLAbelConverse L h hTL hConverse)

end ComplexTorus

end JacobianChallenge

end
