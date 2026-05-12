/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffProper
import JacobianChallenge.Manifold.RiemannSphereR1OverlapReduction
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option diagnostics.threshold 100

/-! # The overlap formula for `chartSCoeffProper`

This file discharges the named open hypothesis
`R1OverlapFormula` (from `RiemannSphereR1OverlapReduction.lean`):

  `chartSCoeffProper om w = -chartNCoeff om w⁻¹ / w^2`  for `w ≠ 0`.

This is the cotangent-bundle transition under the chart transition
`z ↦ 1/z`. Combining it with `zz272`'s continuity at `0` and
`zz271`'s `R1Witness ⇒ genus RS = 0`, R1 is closed
**unconditionally**: `genus RiemannSphere = 0`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- The composition `chartN ∘ chartS.symm` agrees with `z ↦ z⁻¹` on a
neighbourhood of any nonzero `w`. -/
private lemma chartN_comp_chartS_symm_eventually_eq
    {w : ℂ} (hw : w ≠ 0) :
    ((chartN : RiemannSphere → ℂ) ∘ (chartS.symm : ℂ → RiemannSphere))
      =ᶠ[𝓝 w] (fun z : ℂ => z⁻¹) := by
  -- `chartS.symm.trans chartN` has source `{z | z ≠ 0}` and equals `z ↦ z⁻¹`
  -- on that source. The source is open and contains `w`.
  have h_open : IsOpen ({z : ℂ | z ≠ 0}) := isOpen_ne
  have h_mem : w ∈ ({z : ℂ | z ≠ 0}) := hw
  filter_upwards [h_open.mem_nhds h_mem] with z hz
  -- chartS.symm z = some z⁻¹; chartN (some z⁻¹) = z⁻¹.
  show (chartN : RiemannSphere → ℂ) ((chartS.symm : ℂ → RiemannSphere) z) = z⁻¹
  rw [chartS_symm_apply_of_ne hz, chartN_apply_coe]

/-- `fderiv ℂ (chartN ∘ chartS.symm) w = toSpanSingleton ℂ (-(w^2)⁻¹)`
for `w ≠ 0`. -/
private lemma fderiv_chartN_comp_chartS_symm {w : ℂ} (hw : w ≠ 0) :
    fderiv ℂ
      ((chartN : RiemannSphere → ℂ) ∘ (chartS.symm : ℂ → RiemannSphere)) w
      = ContinuousLinearMap.toSpanSingleton ℂ (-(w ^ 2)⁻¹) := by
  rw [(chartN_comp_chartS_symm_eventually_eq hw).fderiv_eq]
  exact fderiv_inv

/-- `extChartAt 𝓘(ℂ, ℂ) ∞ ((w⁻¹ : ℂ) : RiemannSphere) = w`
for `w ≠ 0`. -/
private lemma extChartAt_infty_coe_inv {w : ℂ} (hw : w ≠ 0) :
    extChartAt (𝓘(ℂ, ℂ)) (OnePoint.infty : OnePoint ℂ)
        (((w⁻¹ : ℂ) : RiemannSphere)) = w := by
  show ((chartAt ℂ (OnePoint.infty : OnePoint ℂ)).extend (𝓘(ℂ, ℂ)) :
      RiemannSphere → ℂ) (((w⁻¹ : ℂ) : RiemannSphere)) = w
  rw [show chartAt ℂ (OnePoint.infty : OnePoint ℂ) = chartS from by
    show chartAt' _ = chartS; rw [chartAt'_infty]]
  show ((chartS.extend (𝓘(ℂ, ℂ))) : RiemannSphere → ℂ) (((w⁻¹ : ℂ) : RiemannSphere)) = w
  rw [OpenPartialHomeomorph.extend_coe]
  show (chartS : RiemannSphere → ℂ) (((w⁻¹ : ℂ) : RiemannSphere)) = w
  rw [chartS_apply_coe, inv_inv]

/-- `(extChartAt 𝓘(ℂ, ℂ) ((w⁻¹ : ℂ) : RiemannSphere)).symm` agrees with
`chartN.symm` as functions `ℂ → RiemannSphere`. -/
private lemma extChartAt_coe_inv_symm_eq :
    ((extChartAt (𝓘(ℂ, ℂ)) (((w⁻¹ : ℂ) : RiemannSphere))).symm :
      ℂ → RiemannSphere)
        = (chartN.symm : ℂ → RiemannSphere) := by
  show (((chartAt ℂ (((w⁻¹ : ℂ) : RiemannSphere))).extend
      (𝓘(ℂ, ℂ))).symm : ℂ → RiemannSphere) = chartN.symm
  have h_chart : chartAt ℂ (((w⁻¹ : ℂ) : RiemannSphere)) = chartN := by
    show chartAt' _ = _; rw [chartAt'_coe]
  rw [h_chart]
  rfl

/-- `extChartAt 𝓘(ℂ, ℂ) ∞ .symm` agrees with `chartS.symm`. -/
private lemma extChartAt_infty_symm_eq :
    ((extChartAt (𝓘(ℂ, ℂ)) (OnePoint.infty : OnePoint ℂ)).symm :
      ℂ → RiemannSphere)
        = (chartS.symm : ℂ → RiemannSphere) := by
  show (((chartAt ℂ (OnePoint.infty : OnePoint ℂ)).extend
      (𝓘(ℂ, ℂ))).symm : ℂ → RiemannSphere) = chartS.symm
  have h_chart : chartAt ℂ (OnePoint.infty : OnePoint ℂ) = chartS := by
    show chartAt' _ = _; rw [chartAt'_infty]
  rw [h_chart]
  rfl

/-- `extChartAt 𝓘(ℂ, ℂ) ((w⁻¹ : ℂ) : RiemannSphere)` agrees with `chartN`
as functions `RiemannSphere → ℂ`. -/
private lemma extChartAt_coe_inv_eq :
    (extChartAt (𝓘(ℂ, ℂ)) (((w⁻¹ : ℂ) : RiemannSphere)) : RiemannSphere → ℂ)
        = (chartN : RiemannSphere → ℂ) := by
  show ((chartAt ℂ (((w⁻¹ : ℂ) : RiemannSphere))).extend (𝓘(ℂ, ℂ)) :
      RiemannSphere → ℂ) = chartN
  have h_chart : chartAt ℂ (((w⁻¹ : ℂ) : RiemannSphere)) = chartN := by
    show chartAt' _ = _; rw [chartAt'_coe]
  rw [h_chart]
  rfl

/-- **The overlap formula.** Discharge of `R1OverlapFormula`. -/
theorem chartSCoeffProper_overlap
    (om : HolomorphicOneForm RiemannSphere) {w : ℂ} (hw : w ≠ 0) :
    chartSCoeffProper om w = -chartNCoeff om w⁻¹ / w ^ 2 := by
  unfold chartSCoeffProper
  -- Reduce chartS.symm w to (w⁻¹ : RS).
  have h_symm_w : chartS.symm w = (((w⁻¹ : ℂ) : RiemannSphere)) :=
    chartS_symm_apply_of_ne hw
  rw [h_symm_w]
  -- Compute the cotangent-coord-change via tangent transition.
  rw [cotangentBundleCore_coordChange_apply
    (achart ℂ (((w⁻¹ : ℂ) : RiemannSphere)))
    (achart ℂ (OnePoint.infty : OnePoint ℂ))
    (((w⁻¹ : ℂ) : RiemannSphere))
    (om.toFun (((w⁻¹ : ℂ) : RiemannSphere)))]
  rw [tangentBundleCore_coordChange_achart
    (I := 𝓘(ℂ, ℂ))
    (M := RiemannSphere)
    (OnePoint.infty : OnePoint ℂ)
    (((w⁻¹ : ℂ) : RiemannSphere))
    (((w⁻¹ : ℂ) : RiemannSphere))]
  -- Goal now has fderivWithin ℂ (extChartAt I (w⁻¹:RS) ∘ (extChartAt I ∞).symm)
  --                 (range I) (extChartAt I ∞ (w⁻¹:RS))
  rw [extChartAt_infty_coe_inv hw, extChartAt_infty_symm_eq,
    extChartAt_coe_inv_eq]
  -- Now: fderivWithin ℂ (chartN ∘ chartS.symm) (range 𝓘(ℂ, ℂ)) w
  -- range 𝓘(ℂ, ℂ) = Set.univ.
  rw [show (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = (Set.univ : Set ℂ)
    from ModelWithCorners.range_eq_univ _]
  -- fderivWithin = fderiv on univ.
  rw [fderivWithin_univ]
  rw [fderiv_chartN_comp_chartS_symm hw]
  -- Now compute `ξ.comp (toSpanSingleton ℂ (-(w^2)⁻¹)) 1`.
  -- Let `ξ := om.eval ((w⁻¹:RS)) : ℂ →L[ℂ] ℂ`.
  set ξ : ℂ →L[ℂ] ℂ := om.eval (((w⁻¹ : ℂ) : RiemannSphere)) with hξ_def
  -- `om.toFun = om.eval` for HolomorphicOneForm (both are the underlying section).
  have h_eq : (om.toFun (((w⁻¹ : ℂ) : RiemannSphere)) : ℂ →L[ℂ] ℂ) = ξ := rfl
  -- Compute the composition applied to 1.
  show (ContinuousLinearMap.comp ξ
        (ContinuousLinearMap.toSpanSingleton ℂ (-(w ^ 2)⁻¹))) 1
      = -chartNCoeff om w⁻¹ / w ^ 2
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  -- ξ (1 • -(w^2)⁻¹) = ξ (-(w^2)⁻¹) = -(w^2)⁻¹ • ξ(1) = -(w^2)⁻¹ * ξ(1).
  rw [one_smul]
  have h_smul : (-(w ^ 2)⁻¹ : ℂ) = (-(w ^ 2)⁻¹ : ℂ) • (1 : ℂ) := by
    rw [smul_eq_mul, mul_one]
  rw [h_smul, map_smul, smul_eq_mul]
  -- Now: -(w^2)⁻¹ * ξ 1 = -chartNCoeff om w⁻¹ / w^2.
  have h_coeff : chartNCoeff om w⁻¹ = ξ (1 : ℂ) := by
    show om.eval (chartN.symm (w⁻¹ : ℂ)) (1 : ℂ) = _
    rw [chartN_symm_apply]
  rw [h_coeff]
  field_simp

/-- **R1OverlapFormula is unconditionally true.** -/
theorem R1OverlapFormula_holds : R1OverlapFormula :=
  fun om w hw => chartSCoeffProper_overlap om hw

/-- **Subsingleton(HolomorphicOneForm RiemannSphere) is unconditionally
true.** -/
instance : Subsingleton (HolomorphicOneForm RiemannSphere) :=
  subsingleton_HolomorphicOneForm_of_overlapFormula R1OverlapFormula_holds

/-- **`genus RiemannSphere = 0` is unconditionally true.** -/
theorem genus_RiemannSphere_eq_zero :
    JacobianChallenge.genus RiemannSphere = 0 :=
  genus_RiemannSphere_eq_zero_of_overlapFormula R1OverlapFormula_holds

/-- **Discharge of the named open `genus_RiemannSphere_statement`.** -/
theorem genus_RiemannSphere_statement_holds :
    RiemannSphere.genus_RiemannSphere_statement :=
  genus_RiemannSphere_eq_zero

end RiemannSphere

end JacobianChallenge
