/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDz
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.SmoothPathIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false

/-! # Path-integral formulas for `realComponent (dz L)` and `imagComponent (dz L)`

For any smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, the integrand of
the path integral of `realComponent (dz L)` (resp. `imagComponent (dz L)`)
is exactly `Re ∘ γ.velocity` (resp. `Im ∘ γ.velocity`):

```
γ.integrand (realComponent (dz L)) t = (γ.velocity t).re
γ.integrand (imagComponent (dz L)) t = (γ.velocity t).im
```

This is because `(dz L).eval p = id : ℂ →L[ℂ] ℂ`, so the `realPart` and
`imagPart` of the holomorphic 1-form are pointwise `Re` and `Im`.

Combined with `intervalIntegral_re` / `intervalIntegral_im` (mathlib),
the path integrals become

```
γ.integrate (realComponent (dz L)) = (∫ s in 0..1, γ.velocity s).re
γ.integrate (imagComponent (dz L)) = (∫ s in 0..1, γ.velocity s).im
```

These reduce the boundary-integral computation to a ℂ-valued statement
about velocity integrals on the three faces of a smooth 2-simplex.

## What this file ships

* `ComplexTorus.dz_integrand_realComponent_apply` — pointwise integrand
  formula for `realComponent (dz L)`.
* `ComplexTorus.dz_integrand_imagComponent_apply` — pointwise integrand
  formula for `imagComponent (dz L)`.
* `ComplexTorus.velocity_continuous_torus` — continuity of
  `γ.velocity : ℝ → ℂ` for `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, derived
  from the continuity of `Re ∘ γ.velocity` and `Im ∘ γ.velocity` (which
  are the integrand of `realComponent (dz L)` and `imagComponent (dz L)`
  respectively).
* `ComplexTorus.velocity_intervalIntegrable` — interval integrability
  of `γ.velocity` on `[0, 1]`.
* `ComplexTorus.integrate_realComponent_dz` — `γ.integrate (realComponent
  (dz L)) = (∫ s in 0..1, γ.velocity s).re`.
* `ComplexTorus.integrate_imagComponent_dz` — `γ.integrate (imagComponent
  (dz L)) = (∫ s in 0..1, γ.velocity s).im`.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open MeasureTheory

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Pointwise integrand formulas for `dz` -/

/-- **Pointwise: `applyCotangent ((realComponent (dz L)) p) v = v.re`.**
Public version of the private lemma in `ComplexTorusPeriodValue.lean`. -/
theorem applyCotangent_realComp_dz (p : ℂ ⧸ L) (v : ℂ) :
    SmoothPath.applyCotangent ((realComponent (dz L)) p) v = v.re := by
  unfold SmoothPath.applyCotangent
  show (SmoothPath.cotangentEquiv ((realComponent (dz L)) p) : ℂ →L[ℝ] ℝ) v = v.re
  have h_realComp : ((realComponent (dz L)) p : CotangentSpace 𝓘(ℝ, ℂ) p)
      = (dz L).realPart p := rfl
  rw [h_realComp]
  show ((dz L).realPart p : ℂ →L[ℝ] ℝ) v = v.re
  rw [HolomorphicOneForm.realPart_apply]
  show ((((dz L).eval p) v).re : ℝ) = v.re
  rfl

/-- **Pointwise: `applyCotangent ((imagComponent (dz L)) p) v = v.im`.** -/
theorem applyCotangent_imagComp_dz (p : ℂ ⧸ L) (v : ℂ) :
    SmoothPath.applyCotangent ((imagComponent (dz L)) p) v = v.im := by
  unfold SmoothPath.applyCotangent
  show (SmoothPath.cotangentEquiv ((imagComponent (dz L)) p) : ℂ →L[ℝ] ℝ) v = v.im
  have h_imagComp : ((imagComponent (dz L)) p : CotangentSpace 𝓘(ℝ, ℂ) p)
      = (dz L).imagPart p := rfl
  rw [h_imagComp]
  show ((dz L).imagPart p : ℂ →L[ℝ] ℝ) v = v.im
  rw [HolomorphicOneForm.imagPart_apply]
  show ((((dz L).eval p) v).im : ℝ) = v.im
  rfl

/-- **The `realComponent (dz L)` integrand is `Re ∘ velocity`.**
For any `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` and `t : ℝ`,
`γ.integrand (realComponent (dz L)) t = (γ.velocity t).re`. -/
theorem dz_integrand_realComponent_apply
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (t : ℝ) :
    γ.integrand (realComponent (dz L)) t = (γ.velocity t).re := by
  show SmoothPath.applyCotangent ((realComponent (dz L)) (γ.ambient t))
      (γ.velocity t) = (γ.velocity t).re
  exact applyCotangent_realComp_dz L (γ.ambient t) (γ.velocity t)

/-- **The `imagComponent (dz L)` integrand is `Im ∘ velocity`.** -/
theorem dz_integrand_imagComponent_apply
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (t : ℝ) :
    γ.integrand (imagComponent (dz L)) t = (γ.velocity t).im := by
  show SmoothPath.applyCotangent ((imagComponent (dz L)) (γ.ambient t))
      (γ.velocity t) = (γ.velocity t).im
  exact applyCotangent_imagComp_dz L (γ.ambient t) (γ.velocity t)

/-! ## Continuity and interval integrability of `γ.velocity` -/

/-- **Continuity of `Re ∘ velocity`** for any smooth path on `T_L`.
Direct from `SmoothPath.continuous_integrand` against
`realComponent (dz L)`, since the integrand IS `Re ∘ velocity`. -/
theorem re_velocity_continuous (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    Continuous (fun t : ℝ => (γ.velocity t).re) := by
  have h := SmoothPath.continuous_integrand γ (realComponent (dz L))
  -- `γ.integrand (realComponent (dz L)) = fun t => (γ.velocity t).re`.
  have h_eq : γ.integrand (realComponent (dz L))
      = fun t : ℝ => (γ.velocity t).re := by
    funext t
    exact dz_integrand_realComponent_apply L γ t
  rw [h_eq] at h
  exact h

/-- **Continuity of `Im ∘ velocity`** for any smooth path on `T_L`. -/
theorem im_velocity_continuous (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    Continuous (fun t : ℝ => (γ.velocity t).im) := by
  have h := SmoothPath.continuous_integrand γ (imagComponent (dz L))
  have h_eq : γ.integrand (imagComponent (dz L))
      = fun t : ℝ => (γ.velocity t).im := by
    funext t
    exact dz_integrand_imagComponent_apply L γ t
  rw [h_eq] at h
  exact h

/-- **Continuity of `γ.velocity : ℝ → ℂ`** for any smooth path on `T_L`.
Combines `Re`-continuity and `Im`-continuity via the ℂ ≃ ℝ × ℝ
identification. -/
theorem velocity_continuous_torus (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    Continuous γ.velocity := by
  -- velocity t = ((velocity t).re : ℂ) + I * ((velocity t).im : ℂ).
  have h_eq : γ.velocity
      = fun t : ℝ => ((γ.velocity t).re : ℂ)
          + Complex.I * ((γ.velocity t).im : ℂ) := by
    funext t
    rw [mul_comm Complex.I _]
    exact (Complex.re_add_im (γ.velocity t)).symm
  rw [h_eq]
  have h_re := re_velocity_continuous L γ
  have h_im := im_velocity_continuous L γ
  have h_re_C : Continuous (fun t : ℝ => ((γ.velocity t).re : ℂ)) :=
    Complex.continuous_ofReal.comp h_re
  have h_im_C : Continuous (fun t : ℝ => ((γ.velocity t).im : ℂ)) :=
    Complex.continuous_ofReal.comp h_im
  exact h_re_C.add (continuous_const.mul h_im_C)

/-- **Interval-integrability of `γ.velocity`** on `[0, 1]`. -/
theorem velocity_intervalIntegrable (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    IntervalIntegrable γ.velocity MeasureTheory.volume 0 1 :=
  (velocity_continuous_torus L γ).intervalIntegrable 0 1

/-! ## Path-integral formulas: `Re`/`Im` of the velocity integral -/

/-- **`γ.integrate (realComponent (dz L)) = Re(∫₀..¹ γ.velocity s ds)`.** -/
theorem integrate_realComponent_dz (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    γ.integrate (realComponent (dz L))
      = (∫ s in (0 : ℝ)..1, γ.velocity s).re := by
  -- LHS = ∫₀..¹ γ.integrand (realComponent (dz L)) s ds
  --     = ∫₀..¹ (γ.velocity s).re ds  (by dz_integrand_realComponent_apply)
  --     = Re(∫₀..¹ γ.velocity s ds)  (by intervalIntegral_re).
  rw [SmoothPath.integrate_eq_intervalIntegral]
  -- Goal: ∫ t in 0..1, applyCotangent ((realComponent (dz L)) (γ.ambient t)) (γ.velocity t)
  --       = (∫ s in 0..1, γ.velocity s).re.
  have h_eq : (fun t : ℝ =>
        SmoothPath.applyCotangent ((realComponent (dz L)).toFun (γ.ambient t))
          (γ.velocity t))
      = fun t : ℝ => (γ.velocity t).re := by
    funext t
    exact dz_integrand_realComponent_apply L γ t
  show ∫ t in (0 : ℝ)..1,
      SmoothPath.applyCotangent ((realComponent (dz L)).toFun (γ.ambient t))
        (γ.velocity t)
      = (∫ s in (0 : ℝ)..1, γ.velocity s).re
  rw [h_eq]
  -- ∫ (Re ∘ velocity) = Re (∫ velocity).
  exact intervalIntegral.intervalIntegral_re (velocity_intervalIntegrable L γ)

/-- **`γ.integrate (imagComponent (dz L)) = Im(∫₀..¹ γ.velocity s ds)`.** -/
theorem integrate_imagComponent_dz (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    γ.integrate (imagComponent (dz L))
      = (∫ s in (0 : ℝ)..1, γ.velocity s).im := by
  rw [SmoothPath.integrate_eq_intervalIntegral]
  have h_eq : (fun t : ℝ =>
        SmoothPath.applyCotangent ((imagComponent (dz L)).toFun (γ.ambient t))
          (γ.velocity t))
      = fun t : ℝ => (γ.velocity t).im := by
    funext t
    exact dz_integrand_imagComponent_apply L γ t
  show ∫ t in (0 : ℝ)..1,
      SmoothPath.applyCotangent ((imagComponent (dz L)).toFun (γ.ambient t))
        (γ.velocity t)
      = (∫ s in (0 : ℝ)..1, γ.velocity s).im
  rw [h_eq]
  exact intervalIntegral.intervalIntegral_im (velocity_intervalIntegrable L γ)

end ComplexTorus

end JacobianChallenge

end
