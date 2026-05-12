/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity

set_option linter.unusedSimpArgs false

/-! # Chart coefficient extraction for `HolomorphicOneForm RiemannSphere`

Toward `Subsingleton (HolomorphicOneForm RiemannSphere)` (gating input for
challenge item 14 reverse direction), this file defines the **north** and
**south** chart coefficients of a holomorphic 1-form on the Riemann sphere
and proves their basic algebraic compatibility.

A holomorphic 1-form `om : HolomorphicOneForm RiemannSphere` is, at each
point `x : RiemannSphere`, a continuous `ℂ`-linear functional `ℂ →L[ℂ] ℂ`
on the cotangent fibre — concretely, `om.eval x : ℂ →L[ℂ] ℂ`. Pulling back
along the two charts of the Riemann sphere (`chartN.symm : ℂ → RiemannSphere`
on `{∞}ᶜ` and `chartS.symm : ℂ → RiemannSphere` on `{0 : RS}ᶜ`) and
evaluating at the canonical basis vector `1 : ℂ` produces a pair of
complex-valued functions:

* `chartNCoeff om : ℂ → ℂ`, `chartNCoeff om z = om.eval (chartN.symm z) 1`,
* `chartSCoeff om : ℂ → ℂ`, `chartSCoeff om w = om.eval (chartS.symm w) 1`.

These are the "coefficient of `dz`" (resp. `dw`) of the form in each
chart. The downstream Liouville argument
(`RiemannSphereLiouvilleFromSouthChart.f_eq_zero_of_southChart_continuous`)
needs the overlap transformation `chartSCoeff om w = - chartNCoeff om w⁻¹ / w^2`
on `w ≠ 0` plus regularity. This file lays the algebraic foundation; the
overlap transformation is a separate downstream chip.

## What this file proves (no `sorry`, no `axiom`)

* `chartNCoeff`, `chartSCoeff` — the two coefficient maps.
* `chartNCoeff_zero`, `chartNCoeff_add`, `chartNCoeff_neg`, `chartNCoeff_sub`,
  `chartNCoeff_smul`, and the same for `chartSCoeff` — these are *pointwise*
  linearity, allowing the eventual Subsingleton argument to reduce to
  showing each coefficient vanishes on its chart domain.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace RiemannSphere

/-- **North-chart coefficient.** The coefficient of `dz` of a holomorphic
1-form on the Riemann sphere in the north chart `(some z) ↦ z`. Defined
globally (everywhere on `ℂ`) by pre-composing with `chartN.symm`. -/
def chartNCoeff (om : HolomorphicOneForm RiemannSphere) : ℂ → ℂ :=
  fun z => om.eval (chartN.symm z) 1

/-- **South-chart coefficient.** The coefficient of `dw` of a holomorphic
1-form on the Riemann sphere in the south chart `(some z) ↦ z⁻¹`,
`∞ ↦ 0`. Defined globally (everywhere on `ℂ`, including `w = 0`, where
`chartS.symm 0 = ∞`) by pre-composing with `chartS.symm`. -/
def chartSCoeff (om : HolomorphicOneForm RiemannSphere) : ℂ → ℂ :=
  fun w => om.eval (chartS.symm w) 1

/-! ### Pointwise linearity of `chartNCoeff` -/

@[simp]
theorem chartNCoeff_zero :
    chartNCoeff (0 : HolomorphicOneForm RiemannSphere) = 0 := by
  funext z
  simp [chartNCoeff, HolomorphicOneForm.eval_zero]

theorem chartNCoeff_add (om₁ om₂ : HolomorphicOneForm RiemannSphere) :
    chartNCoeff (om₁ + om₂) = chartNCoeff om₁ + chartNCoeff om₂ := by
  funext z
  simp [chartNCoeff, HolomorphicOneForm.eval_add_apply]

theorem chartNCoeff_neg (om : HolomorphicOneForm RiemannSphere) :
    chartNCoeff (-om) = -chartNCoeff om := by
  funext z
  simp [chartNCoeff, HolomorphicOneForm.eval_neg_apply]

theorem chartNCoeff_sub (om₁ om₂ : HolomorphicOneForm RiemannSphere) :
    chartNCoeff (om₁ - om₂) = chartNCoeff om₁ - chartNCoeff om₂ := by
  funext z
  simp [chartNCoeff, HolomorphicOneForm.eval_sub_apply]

theorem chartNCoeff_smul (c : ℂ) (om : HolomorphicOneForm RiemannSphere) :
    chartNCoeff (c • om) = c • chartNCoeff om := by
  funext z
  simp [chartNCoeff, HolomorphicOneForm.eval_smul_apply, smul_eq_mul]

/-! ### Pointwise linearity of `chartSCoeff` -/

@[simp]
theorem chartSCoeff_zero :
    chartSCoeff (0 : HolomorphicOneForm RiemannSphere) = 0 := by
  funext w
  simp [chartSCoeff, HolomorphicOneForm.eval_zero]

theorem chartSCoeff_add (om₁ om₂ : HolomorphicOneForm RiemannSphere) :
    chartSCoeff (om₁ + om₂) = chartSCoeff om₁ + chartSCoeff om₂ := by
  funext w
  simp [chartSCoeff, HolomorphicOneForm.eval_add_apply]

theorem chartSCoeff_neg (om : HolomorphicOneForm RiemannSphere) :
    chartSCoeff (-om) = -chartSCoeff om := by
  funext w
  simp [chartSCoeff, HolomorphicOneForm.eval_neg_apply]

theorem chartSCoeff_sub (om₁ om₂ : HolomorphicOneForm RiemannSphere) :
    chartSCoeff (om₁ - om₂) = chartSCoeff om₁ - chartSCoeff om₂ := by
  funext w
  simp [chartSCoeff, HolomorphicOneForm.eval_sub_apply]

theorem chartSCoeff_smul (c : ℂ) (om : HolomorphicOneForm RiemannSphere) :
    chartSCoeff (c • om) = c • chartSCoeff om := by
  funext w
  simp [chartSCoeff, HolomorphicOneForm.eval_smul_apply, smul_eq_mul]

/-! ### Bridge identities

These re-express `chartNCoeff` and `chartSCoeff` as the pointwise
evaluation of `om.eval` at the underlying chart-pullback point, so
downstream files can rewrite freely between the two perspectives. -/

theorem chartNCoeff_apply (om : HolomorphicOneForm RiemannSphere) (z : ℂ) :
    chartNCoeff om z = om.eval (((z : ℂ) : RiemannSphere)) 1 := by
  unfold chartNCoeff
  rw [chartN_symm_apply]

theorem chartSCoeff_apply_of_ne (om : HolomorphicOneForm RiemannSphere)
    {w : ℂ} (hw : w ≠ 0) :
    chartSCoeff om w = om.eval (((w⁻¹ : ℂ) : RiemannSphere)) 1 := by
  unfold chartSCoeff
  rw [chartS_symm_apply_of_ne hw]

theorem chartSCoeff_zero_apply (om : HolomorphicOneForm RiemannSphere) :
    chartSCoeff om 0 = om.eval (OnePoint.infty : RiemannSphere) 1 := by
  unfold chartSCoeff
  rw [chartS_symm_apply_zero]

end RiemannSphere

end JacobianChallenge

end
