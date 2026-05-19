/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.ComplexTorusPathConnected
import JacobianChallenge.Manifold.ComplexTorusPeriodValue

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

/-! # Period of `dz` along the basepoint-0 smooth path `α L Q`

The path `α L Q : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` (from `0` to `Q`) has
the same ambient shape as `torusBasisLoop` — both parameterise
`t ↦ π((t : ℂ) * z)` for some complex number `z` (with `z := Q.out`
for `α` vs `z := lam` for `torusBasisLoop`). Reusing the
foundational identities `mfderiv_torusBasisAmbient_apply_one` and
`applyCotangent_realComp_dz_local` / `_imagComp_dz`, we obtain

  `complexChainPeriod (single (α L Q)) (dz L) = Q.out`.

This is the analytic ingredient for the Abel-Jacobi point map on the
complex torus: `B.abelJacobiPoint Q = [Q.out] mod periodLatticeImage`
when `B.pathFromBase = α L`, hence `AnalyticJacobianSymp ≅ T_L` via the
identification `periodLatticeImage ≅ L`.

No `sorry`, no `axiom`. -/

open Set Metric MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Re-exposed cotangent simplifications

Local clones of `ComplexTorusPeriodValue.lean`'s `private` lemmas (so
they can be reused here without changing visibility upstream). -/

private lemma applyCotangent_realComp_dz_local (p : ℂ ⧸ L) (v : ℂ) :
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

private lemma applyCotangent_imagComp_dz_local (p : ℂ ⧸ L) (v : ℂ) :
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

/-! ## `α L Q`'s ambient agrees with `torusBasisAmbient L Q.out` on `[0,1]` -/

private lemma α_ambient_eqOn
    (Q : ℂ ⧸ L) :
    ∀ u, u ∈ Set.Icc (0 : ℝ) 1 →
      (α L Q).ambient u = torusBasisAmbient L Q.out u := by
  intro u hu
  have hu_uI : u ∈ unitInterval := hu
  have h := (α L Q).ambient_eq_on_unitInterval (⟨u, hu_uI⟩ : unitInterval)
  -- (α L Q).toPath at ⟨u, hu_uI⟩ unfolds to L.mkQ ((u : ℂ) * Q.out).
  show (α L Q).ambient u = L.mkQ ((u : ℂ) * Q.out)
  exact h.trans rfl

/-! ## Integration: (α L Q).integrate (realComp dz) = Q.out.re -/

theorem α_integrate_realComp_dz (Q : ℂ ⧸ L) :
    (α L Q).integrate (realComponent (dz L)) = Q.out.re := by
  unfold SmoothPath.integrate
  rw [SmoothPath.intervalIntegral_integrand_eq_of_ambient_eqOn_Icc_fun
        (γ := α L Q) (f := torusBasisAmbient L Q.out)
        (s := 0) (t := 1) zero_le_one
        (α_ambient_eqOn L Q)
        (realComponent (dz L))]
  have h_ptwise : ∀ u : ℝ,
      SmoothPath.applyCotangent ((realComponent (dz L)) (torusBasisAmbient L Q.out u))
          ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (torusBasisAmbient L Q.out) u
            : ℝ →L[ℝ] _) (1 : ℝ))
        = Q.out.re := by
    intro u
    rw [applyCotangent_realComp_dz_local L (torusBasisAmbient L Q.out u)]
    have h_vel : (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out) u
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out u)) (1 : ℝ))
        : ℂ) = Q.out :=
      mfderiv_torusBasisAmbient_apply_one L Q.out u
    change (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out) u
            : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out u)) (1 : ℝ))
            : ℂ).re = Q.out.re
    rw [h_vel]
  simp_rw [h_ptwise]
  simp

theorem α_integrate_imagComp_dz (Q : ℂ ⧸ L) :
    (α L Q).integrate (imagComponent (dz L)) = Q.out.im := by
  unfold SmoothPath.integrate
  rw [SmoothPath.intervalIntegral_integrand_eq_of_ambient_eqOn_Icc_fun
        (γ := α L Q) (f := torusBasisAmbient L Q.out)
        (s := 0) (t := 1) zero_le_one
        (α_ambient_eqOn L Q)
        (imagComponent (dz L))]
  have h_ptwise : ∀ u : ℝ,
      SmoothPath.applyCotangent ((imagComponent (dz L)) (torusBasisAmbient L Q.out u))
          ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (torusBasisAmbient L Q.out) u
            : ℝ →L[ℝ] _) (1 : ℝ))
        = Q.out.im := by
    intro u
    rw [applyCotangent_imagComp_dz_local L (torusBasisAmbient L Q.out u)]
    have h_vel : (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out) u
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out u)) (1 : ℝ))
        : ℂ) = Q.out :=
      mfderiv_torusBasisAmbient_apply_one L Q.out u
    change (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out) u
            : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L Q.out u)) (1 : ℝ))
            : ℂ).im = Q.out.im
    rw [h_vel]
  simp_rw [h_ptwise]
  simp

/-! ## Headline: `complexChainPeriod (single (α L Q)) (dz L) = Q.out` -/

/-- **Chain-level period of `dz` along the basepoint-0 path `α L Q`.**
`complexChainPeriod (single (α L Q)) (dz L) = Q.out`. -/
theorem complexChainPeriod_single_α_dz (Q : ℂ ⧸ L) :
    complexChainPeriod (SmoothChain.single (α L Q)) (dz L) = Q.out := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single]
  rw [α_integrate_realComp_dz, α_integrate_imagComp_dz]
  -- Combine real and imag parts to recover Q.out.
  have h : ((Q.out.re : ℝ) : ℂ) + Complex.I * ((Q.out.im : ℝ) : ℂ) = Q.out := by
    have := Complex.re_add_im Q.out
    linear_combination this
  exact h

end ComplexTorus

end JacobianChallenge

end
