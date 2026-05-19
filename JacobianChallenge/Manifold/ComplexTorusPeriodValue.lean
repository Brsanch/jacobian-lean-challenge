/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusPeriodComputation
import JacobianChallenge.Manifold.ComplexTorusDz
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.SmoothPathVelocityFromFun
import JacobianChallenge.Manifold.ComplexPeriodPairing
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

/-! # Period of `dz` over `torusBasisLoop lam` equals `lam`

End-to-end period computation:

  `complexPeriod (torusBasisLoop lam hlam).singleCycle (dz L) = lam`

Composes the foundational chips:

* `mfderiv_torusBasisAmbient_apply_one`: velocity of `mkQ ∘ (·*lam)` = lam.
* `dz_apply`: `dz L` evaluates pointwise to `ContinuousLinearMap.id ℂ ℂ`.
* `HolomorphicOneForm.realPart_apply` / `imagPart_apply` (from
  `HolomorphicOneFormRealification`): `om.realPart x v = (om.eval x v).re`.
* `intervalIntegral_integrand_eq_of_ambient_eqOn_Icc_fun` (existing
  in `SmoothPathVelocityFromFun`).

## What this file ships

* `ComplexTorus.torusBasisLoop_integrate_realComp_dz`,
  `_imagComp_dz`: the real/imag period of `dz` along `γ_lam`.
* `ComplexTorus.complexPeriod_torusBasisLoop_dz`:
  `complexPeriod γ_lam.singleCycle (dz L) = lam`.

No `sorry`, no `axiom`. -/

open Set Metric MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `γ_lam.ambient` agrees with `torusBasisAmbient` on `[0,1]` -/

private lemma torusBasisLoop_ambient_eqOn
    (lam : ℂ) (hlam : lam ∈ L) :
    ∀ u, u ∈ Set.Icc (0 : ℝ) 1 →
      (torusBasisLoop lam hlam).ambient u = torusBasisAmbient L lam u := by
  intro u hu
  have hu_uI : u ∈ unitInterval := hu
  -- (torusBasisLoop).ambient _ = toPath _ on unitInterval.
  -- For our t = ⟨u, hu_uI⟩, the val is `u` and ambient u = toPath ⟨u, _⟩.
  -- The toPath at ⟨u, _⟩ for torusBasisLoop unfolds to L.mkQ ((u : ℂ) * lam).
  have h := (torusBasisLoop lam hlam).ambient_eq_on_unitInterval
    (⟨u, hu_uI⟩ : unitInterval)
  -- h : (torusBasisLoop lam hlam).ambient u = (torusBasisLoop lam hlam).toPath ⟨u, hu_uI⟩.
  -- (·.val) of `⟨u, hu_uI⟩` is `u` definitionally; RHS unfolds to mkQ ((u : ℂ) * lam).
  show (torusBasisLoop lam hlam).ambient u = L.mkQ ((u : ℂ) * lam)
  exact h.trans rfl

/-! ## Integrand simplification -/

private lemma applyCotangent_realComp_dz (p : ℂ ⧸ L) (v : ℂ) :
    SmoothPath.applyCotangent ((realComponent (dz L)) p) v = v.re := by
  -- `applyCotangent φ v` unfolds to `cotangentEquiv φ v`. cotangentEquiv is
  -- identity-on-data so `cotangentEquiv φ : ℂ →L[ℝ] ℝ` is just φ coerced.
  -- (realComponent (dz L)) p : CotangentSpace _ p = ℂ →L[ℝ] ℝ is
  --   (dz L).realPart p (by realComponent def).
  -- (dz L).realPart p v = ((dz L).eval p v).re by HolomorphicOneForm.realPart_apply.
  -- (dz L).eval p = id (definitionally), so id v = v, and v.re = v.re.
  unfold SmoothPath.applyCotangent
  show (SmoothPath.cotangentEquiv ((realComponent (dz L)) p) : ℂ →L[ℝ] ℝ) v = v.re
  -- cotangentEquiv is identity on data — its forward is the type-coercion.
  -- We work with (realComponent (dz L)) p viewed as the underlying ℂ →L[ℝ] ℝ.
  -- (realComponent (dz L)) p = (dz L).realPart p as elements of CotangentSpace.
  have h_realComp : ((realComponent (dz L)) p : CotangentSpace 𝓘(ℝ, ℂ) p)
      = (dz L).realPart p := rfl
  rw [h_realComp]
  -- The cotangentEquiv of (dz L).realPart p is itself ((·) viewed as ℂ →L[ℝ] ℝ).
  show ((dz L).realPart p : ℂ →L[ℝ] ℝ) v = v.re
  rw [HolomorphicOneForm.realPart_apply]
  -- ((dz L).eval p v).re = v.re. (dz L).eval p = id (definitionally).
  show ((((dz L).eval p) v).re : ℝ) = v.re
  rfl

private lemma applyCotangent_imagComp_dz (p : ℂ ⧸ L) (v : ℂ) :
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

/-! ## Integration: γ_lam.integrate (realComp dz) = lam.re -/

theorem torusBasisLoop_integrate_realComp_dz
    (lam : ℂ) (hlam : lam ∈ L) :
    (torusBasisLoop lam hlam).integrate (realComponent (dz L)) = lam.re := by
  unfold SmoothPath.integrate
  rw [SmoothPath.intervalIntegral_integrand_eq_of_ambient_eqOn_Icc_fun
        (γ := torusBasisLoop lam hlam) (f := torusBasisAmbient L lam)
        (s := 0) (t := 1) zero_le_one
        (torusBasisLoop_ambient_eqOn L lam hlam)
        (realComponent (dz L))]
  have h_ptwise : ∀ u : ℝ,
      SmoothPath.applyCotangent ((realComponent (dz L)) (torusBasisAmbient L lam u))
          ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (torusBasisAmbient L lam) u
            : ℝ →L[ℝ] _) (1 : ℝ))
        = lam.re := by
    intro u
    rw [applyCotangent_realComp_dz L (torusBasisAmbient L lam u)]
    have h_vel : (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L lam) u
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L lam u)) (1 : ℝ))
        : ℂ) = lam :=
      mfderiv_torusBasisAmbient_apply_one L lam u
    change (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L lam) u
            : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L lam u)) (1 : ℝ))
            : ℂ).re = lam.re
    rw [h_vel]
  simp_rw [h_ptwise]
  simp

theorem torusBasisLoop_integrate_imagComp_dz
    (lam : ℂ) (hlam : lam ∈ L) :
    (torusBasisLoop lam hlam).integrate (imagComponent (dz L)) = lam.im := by
  unfold SmoothPath.integrate
  rw [SmoothPath.intervalIntegral_integrand_eq_of_ambient_eqOn_Icc_fun
        (γ := torusBasisLoop lam hlam) (f := torusBasisAmbient L lam)
        (s := 0) (t := 1) zero_le_one
        (torusBasisLoop_ambient_eqOn L lam hlam)
        (imagComponent (dz L))]
  have h_ptwise : ∀ u : ℝ,
      SmoothPath.applyCotangent ((imagComponent (dz L)) (torusBasisAmbient L lam u))
          ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (torusBasisAmbient L lam) u
            : ℝ →L[ℝ] _) (1 : ℝ))
        = lam.im := by
    intro u
    rw [applyCotangent_imagComp_dz L (torusBasisAmbient L lam u)]
    have h_vel : (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L lam) u
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L lam u)) (1 : ℝ))
        : ℂ) = lam :=
      mfderiv_torusBasisAmbient_apply_one L lam u
    change (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L lam) u
            : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L lam u)) (1 : ℝ))
            : ℂ).im = lam.im
    rw [h_vel]
  simp_rw [h_ptwise]
  simp

/-! ## Period: `complexPeriod (γ_lam.singleCycle) dz = lam` -/

/-- `SmoothCycle.integrate c ω` where c is a single-loop cycle, reduces
to `γ.integrate ω`. -/
private lemma smoothCycle_integrate_single_smoothLoop
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_loop : γ.src = γ.tgt)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    SmoothCycle.integrate (single_smoothLoop_smoothCycle γ h_loop) om
      = γ.integrate om := by
  -- single_smoothLoop_smoothCycle uses SmoothChain.single, whose integrate = path integrate.
  rw [SmoothCycle.integrate_eq]
  rw [single_smoothLoop_smoothCycle_coe]
  rw [SmoothChain.integrate_single]

/-- **Period of `dz` over a torus basis loop equals the lattice
generator.** `complexPeriod ((torusBasisLoop lam).singleCycle) (dz L)
= lam` for any `lam ∈ L`. -/
theorem complexPeriod_torusBasisLoop_dz
    (lam : ℂ) (hlam : lam ∈ L) :
    complexPeriod
      (single_smoothLoop_smoothCycle (torusBasisLoop lam hlam)
        ((torusBasisLoop_src lam hlam).trans (torusBasisLoop_tgt lam hlam).symm))
      (dz L) = lam := by
  unfold complexPeriod
  rw [smoothCycle_integrate_single_smoothLoop, smoothCycle_integrate_single_smoothLoop]
  rw [torusBasisLoop_integrate_realComp_dz L lam hlam,
      torusBasisLoop_integrate_imagComp_dz L lam hlam]
  -- (lam.re : ℝ : ℂ) + I * (lam.im : ℝ : ℂ) = lam.
  -- Use Complex.re_add_im : (↑z.re + ↑z.im * I = z). Rearrange.
  have h : ((lam.re : ℝ) : ℂ) + Complex.I * ((lam.im : ℝ) : ℂ) = lam := by
    have := Complex.re_add_im lam
    -- this : (↑lam.re + ↑lam.im * I = lam).
    linear_combination this
  exact h

end ComplexTorus

end JacobianChallenge

end
