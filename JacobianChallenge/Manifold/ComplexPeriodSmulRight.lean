/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexPeriodPairing
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity

/-! # ℂ-scaling of `complexPeriod` in the form argument (PL-3e follow-up)

This file completes ℂ-linearity of the complex-valued period pairing
`complexPeriod : SmoothCycle 𝓘(ℝ, ℂ) X → HolomorphicOneForm X → ℂ` in
the form argument. PL-3e (in `SmoothPathIntegrability.lean`) already
delivered additivity (`complexPeriod_add_right`); the remaining piece is
ℂ-scaling, which is *algebraic* — it mixes the real and imaginary
components via the complex-multiplication identity

    `realPart (z • om) = (Re z) · realPart om − (Im z) · imagPart om`
    `imagPart (z • om) = (Re z) · imagPart om + (Im z) · realPart om`

(i.e. multiplication by `z = a + bi` rotates `(realPart, imagPart)`
through the matrix `((a, -b), (b, a))` pointwise). Composed with the
real-side `SmoothCycle.integrate_smul_right` and
`SmoothCycle.integrate_add_form`, the four-term combination assembles
back to `z · complexPeriod c om`.

## Main results

* `HolomorphicOneForm.realPart_smul_apply` /
  `HolomorphicOneForm.imagPart_smul_apply` — pointwise.
* `HolomorphicOneForm.realPart_smul` / `imagPart_smul` — bundled `ℂ →L[ℝ] ℝ`
  identities (Re/Im components after ℂ-scaling).
* `JacobianChallenge.realComponent_smul` / `imagComponent_smul` — bundled
  `SmoothOneForm` identities (each side of which is a smooth section).
* `JacobianChallenge.complexPeriod_smul_right` — the headline.
* `JacobianChallenge.complexPeriodLinearMap` — the bundled
  `HolomorphicOneForm X →ₗ[ℂ] ℂ` (with the cycle held fixed). Composes
  the additive `complexPeriodHomRight` (PL-3e) with this ℂ-scaling.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Pointwise ℂ-scaling identities on `realPart` / `imagPart` -/

theorem realPart_smul_apply (z : ℂ) (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (z • om).realPart x v = z.re * om.realPart x v - z.im * om.imagPart x v := by
  rw [realPart_apply, eval_smul_apply, realPart_apply, imagPart_apply]
  exact Complex.mul_re z (om.eval x v)

theorem imagPart_smul_apply (z : ℂ) (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (z • om).imagPart x v = z.re * om.imagPart x v + z.im * om.realPart x v := by
  rw [imagPart_apply, eval_smul_apply, imagPart_apply, realPart_apply]
  exact Complex.mul_im z (om.eval x v)

/-! ## Bundled `ℂ →L[ℝ] ℝ`-valued identities -/

theorem realPart_smul (z : ℂ) (om : HolomorphicOneForm X) (x : X) :
    (z • om).realPart x = z.re • om.realPart x - z.im • om.imagPart x := by
  ext v
  rw [realPart_smul_apply]
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem imagPart_smul (z : ℂ) (om : HolomorphicOneForm X) (x : X) :
    (z • om).imagPart x = z.re • om.imagPart x + z.im • om.realPart x := by
  ext v
  rw [imagPart_smul_apply]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

end HolomorphicOneForm

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-! ## Bundled `SmoothOneForm`-valued identities (lifting `realPart_smul` etc.
through `realComponent` / `imagComponent`) -/

/-- The real component of a ℂ-scalar multiple decomposes as
`Re z • realComponent om - Im z • imagComponent om`. Sections agree on
both sides pointwise via `realPart_smul`. -/
@[simp] lemma realComponent_smul (z : ℂ) (om : HolomorphicOneForm X) :
    realComponent (z • om)
      = z.re • realComponent om - z.im • imagComponent om := by
  refine ContMDiffSection.coe_inj ?_
  funext x
  exact HolomorphicOneForm.realPart_smul z om x

/-- The imaginary component of a ℂ-scalar multiple decomposes as
`Re z • imagComponent om + Im z • realComponent om`. -/
@[simp] lemma imagComponent_smul (z : ℂ) (om : HolomorphicOneForm X) :
    imagComponent (z • om)
      = z.re • imagComponent om + z.im • realComponent om := by
  refine ContMDiffSection.coe_inj ?_
  funext x
  exact HolomorphicOneForm.imagPart_smul z om x

/-! ## ℂ-scaling of `complexPeriod` in the form arg -/

/-- **Form-side ℂ-scaling of the complex period pairing.** The four-term
real-side combination
`(Re z R − Im z I) + i (Re z I + Im z R) = (Re z + i Im z)(R + i I)`
reassembles back to `z · complexPeriod c om`. Uses
`SmoothCycle.integrate_smul_right` (real-scaling) and
`SmoothCycle.integrate_add_form` (PL-3e additivity). -/
theorem complexPeriod_smul_right (c : SmoothCycle 𝓘(ℝ, ℂ) X) (z : ℂ)
    (om : HolomorphicOneForm X) :
    complexPeriod c (z • om) = z * complexPeriod c om := by
  unfold complexPeriod
  -- Substitute the bundled smul identities for the real/imag components.
  rw [realComponent_smul, imagComponent_smul]
  -- Expand each real-side integral via `integrate_add_form` + `integrate_smul_right`
  -- (note: `(a • x - b • y) = (a • x) + (-b • y)` so we route through `_add_form`
  -- after rewriting `sub` as `add (neg)`).
  rw [show (z.re • realComponent om - z.im • imagComponent om)
        = z.re • realComponent om + (-z.im) • imagComponent om from by
      rw [sub_eq_add_neg, neg_smul],
    SmoothCycle.integrate_add_form,
    SmoothCycle.integrate_smul_right, SmoothCycle.integrate_smul_right,
    SmoothCycle.integrate_add_form,
    SmoothCycle.integrate_smul_right, SmoothCycle.integrate_smul_right]
  -- Goal: a pure complex-arithmetic identity, split via `Complex.ext`.
  set R : ℝ := SmoothCycle.integrate c (realComponent om)
  set Im : ℝ := SmoothCycle.integrate c (imagComponent om)
  -- Both sides are casts of real polynomials in `(z.re, z.im, R, Im)` after
  -- decomposing `z` and `complexPeriod`'s reassembly. Split into Re/Im.
  apply Complex.ext
  all_goals
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  all_goals try ring

/-! ## Bundled `HolomorphicOneForm X →ₗ[ℂ] ℂ` -/

/-- The complex-valued period pairing as a **ℂ-linear** map in the form
argument, with the smooth cycle held fixed. Composes the additive
`complexPeriodHomRight` (PL-3e) with the ℂ-scaling identity above. -/
def complexPeriodLinearMap (c : SmoothCycle 𝓘(ℝ, ℂ) X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun om := complexPeriod c om
  map_add' om₁ om₂ := complexPeriod_add_right c om₁ om₂
  map_smul' z om := by
    -- `(z • om) ↦ complexPeriod c (z • om) = z * complexPeriod c om
    --                                       = z • complexPeriod c om`
    -- (the last step is `smul_eq_mul` on `ℂ`).
    change complexPeriod c (z • om) = z • complexPeriod c om
    rw [complexPeriod_smul_right, smul_eq_mul]

@[simp] lemma complexPeriodLinearMap_apply (c : SmoothCycle 𝓘(ℝ, ℂ) X)
    (om : HolomorphicOneForm X) :
    complexPeriodLinearMap c om = complexPeriod c om := rfl

end JacobianChallenge

end
