/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalSimplexSmoothLift
import JacobianChallenge.Manifold.ComplexTorusDzBoundaryIntegralFormula
import JacobianChallenge.Manifold.ComplexTorusMkQMfderiv
import JacobianChallenge.Manifold.Smooth2Simplex
import JacobianChallenge.Manifold.SmoothPathIntegral
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # FTC identity for face velocity integrals via the global smooth lift

For `σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)` and its global smooth lift
`F := globalSimplexContLift L σ`, each face's velocity integral
identifies with the difference of `F`-values at the face endpoints:

```
∫ s in 0..1, (face_i σ).velocity s = F(face_i_param 1) - F(face_i_param 0)
```

Telescoping the three differences gives
`boundary_face_velocity_integral L σ = 0`, hence
`RealImagDzInCanonicalClosed L` holds unconditionally.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology
open MeasureTheory

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Chain-rule identification of mfderivs -/

/-- `((mfderiv σ.toFun) p) v = ((mfderiv F) p) v` as elements of ℂ. -/
private lemma mfderiv_σ_apply_eq_mfderiv_F_apply
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (p v : Fin 2 → ℝ) :
    ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) σ.toFun p
        : (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (σ.toFun p)) v : ℂ)
      = ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ)
            (fun q => (globalSimplexContLift L σ q : ℂ)) p
          : (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
            (globalSimplexContLift L σ p)) v : ℂ) := by
  have h_eq : σ.toFun = (L.mkQ : ℂ → ℂ ⧸ L) ∘
      fun q => (globalSimplexContLift L σ q : ℂ) := by
    funext q
    exact (globalSimplexContLift_lifts L σ q).symm
  have h_F_smooth : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun q => (globalSimplexContLift L σ q : ℂ)) :=
    globalSimplexContLift_contMDiff L σ
  have h_F_diff : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ)
      (fun q => (globalSimplexContLift L σ q : ℂ)) p :=
    (h_F_smooth p).mdifferentiableAt (by decide)
  have h_mkQ_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (L.mkQ : ℂ → ℂ ⧸ L) :=
    mkQ_contMDiff_real L 1
  have h_mkQ_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (L.mkQ : ℂ → ℂ ⧸ L) (globalSimplexContLift L σ p) :=
    (h_mkQ_smooth (globalSimplexContLift L σ p)).mdifferentiableAt one_ne_zero
  -- Chain rule: mfderiv (mkQ ∘ F) p applied to v = mfderiv mkQ (F p) applied to (mfderiv F p v).
  have h_chain :=
    mfderiv_comp_apply (I := 𝓘(ℝ, Fin 2 → ℝ)) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℂ))
      (f := fun q => (globalSimplexContLift L σ q : ℂ))
      (g := (L.mkQ : ℂ → ℂ ⧸ L)) (x := p) h_mkQ_diff h_F_diff v
  -- LHS via h_eq: ((mfderiv σ.toFun) p) v = ((mfderiv (mkQ ∘ F)) p) v.
  have h_lhs_eq :
      ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) σ.toFun p
          : (Fin 2 → ℝ) →L[ℝ] _) v : ℂ)
        = ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ)
              ((L.mkQ : ℂ → ℂ ⧸ L) ∘ fun q => (globalSimplexContLift L σ q : ℂ)) p
            : (Fin 2 → ℝ) →L[ℝ] _) v : ℂ) := by
    rw [h_eq]
  -- After h_chain and mfderiv_mkQ_apply, RHS of h_lhs_eq becomes ((mfderiv F p) v : ℂ).
  rw [h_lhs_eq, h_chain]
  exact mfderiv_mkQ_apply L _ _

/-! ## Velocity = HasDerivAt of F ∘ param -/

/-- The composite `F ∘ face_i_param : ℝ → ℂ` is `ContMDiff ∞`. -/
private lemma F_comp_param_contMDiff
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (param : ℝ → (Fin 2 → ℝ))
    (h_param : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ param) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (globalSimplexContLift L σ (param t) : ℂ)) :=
  (globalSimplexContLift_contMDiff L σ).comp h_param

/-- For `t ∈ Ioo 0 1`, the face's velocity equals the derivative of
`F ∘ face_i_param` at `t`. -/
private lemma face_velocity_HasDerivAt_F_comp
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (param : ℝ → (Fin 2 → ℝ))
    (h_param : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ param)
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (h_amb_eq : ∀ s ∈ Set.Ioo (0 : ℝ) 1, SmoothPath.ambient γ s = σ.toFun (param s))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => (globalSimplexContLift L σ (param s) : ℂ))
      (SmoothPath.velocity γ t) t := by
  -- F_param := F ∘ param : ℝ → ℂ smooth (ContMDiff ∞).
  set F_param : ℝ → ℂ := fun s : ℝ => (globalSimplexContLift L σ (param s) : ℂ)
  have h_F_param_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ F_param :=
    F_comp_param_contMDiff L σ param h_param
  -- ContMDiff ∞ for ℝ → ℂ ⟹ ContDiff ℝ ∞ F_param.
  have h_F_param_cd : ContDiff ℝ ∞ F_param :=
    (contMDiff_iff_contDiff (f := F_param) (n := ∞)).mp h_F_param_smooth
  have h_F_param_diffAt : DifferentiableAt ℝ F_param t :=
    (h_F_param_cd.differentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0)).differentiableAt
  have h_F_param_hasDeriv : HasDerivAt F_param (deriv F_param t) t :=
    h_F_param_diffAt.hasDerivAt
  -- Reduce to showing: deriv F_param t = γ.velocity t.
  rw [show SmoothPath.velocity γ t = deriv F_param t from ?_]
  · exact h_F_param_hasDeriv
  -- deriv F_param t = (mfderiv F_param t) 1.
  rw [show deriv F_param t
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) F_param t : ℝ →L[ℝ] _) (1 : ℝ) from ?_]
  · -- γ.velocity t = mfderiv γ.ambient t (1).
    -- On Ioo 0 1 (open nbhd of t), γ.ambient = σ.toFun ∘ param.
    have h_ev : (SmoothPath.ambient γ : ℝ → ℂ ⧸ L) =ᶠ[𝓝 t]
        (fun s => σ.toFun (param s)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun s hs => h_amb_eq s hs)
    have h_mfderiv_amb : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (SmoothPath.ambient γ) t
        = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun s => σ.toFun (param s)) t :=
      h_ev.mfderiv_eq
    -- Chain rule for σ ∘ param.
    have h_σ_diff : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) σ.toFun (param t) :=
      (σ.smooth (param t)).mdifferentiableAt (by decide)
    have h_param_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) param t :=
      (h_param t).mdifferentiableAt (by decide)
    have h_F_diff : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ)
        (fun q => (globalSimplexContLift L σ q : ℂ)) (param t) :=
      ((globalSimplexContLift_contMDiff L σ) (param t)).mdifferentiableAt (by decide)
    have h_chain_σ :=
      mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Fin 2 → ℝ)) (I'' := 𝓘(ℝ, ℂ))
        (f := param) (g := σ.toFun) (x := t) h_σ_diff h_param_diff (1 : ℝ)
    have h_chain_F :=
      mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Fin 2 → ℝ)) (I'' := 𝓘(ℝ, ℂ))
        (f := param) (g := fun q => (globalSimplexContLift L σ q : ℂ))
        (x := t) h_F_diff h_param_diff (1 : ℝ)
    have h_v := mfderiv_σ_apply_eq_mfderiv_F_apply L σ (param t)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) param t : ℝ →L[ℝ] _) (1 : ℝ))
    -- Use h_mfderiv_amb to switch γ.ambient ↦ σ ∘ param.
    -- Note: h_mfderiv_amb gives mfderiv γ.ambient t = mfderiv (σ ∘ param) t (both as CLMs).
    -- We need to apply both sides to 1. The TangentSpace fiber is ℂ at both points.
    -- Step: γ.velocity t = mfderiv γ.ambient t (1) by definition.
    change ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (SmoothPath.ambient γ) t
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (SmoothPath.ambient γ t)) (1 : ℝ) : ℂ)
        = ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) F_param t : ℝ →L[ℝ] _) (1 : ℝ) : ℂ)
    -- Swap γ.ambient to σ ∘ param via h_mfderiv_amb.
    rw [show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (SmoothPath.ambient γ) t
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (SmoothPath.ambient γ t))
        = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (σ.toFun ∘ param) t from h_mfderiv_amb]
    -- Chain rules via Eq.trans (avoids universe-metavar issues in `rw`).
    have step1 : ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (σ.toFun ∘ param) t
            : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) ((σ.toFun ∘ param) t)) (1 : ℝ) : ℂ)
        = ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) σ.toFun (param t)
            : (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (σ.toFun (param t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) param t
              : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (param t)) (1 : ℝ)) : ℂ) := by
      have := h_chain_σ
      exact_mod_cast this
    have step2 : ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) σ.toFun (param t)
            : (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (σ.toFun (param t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) param t
              : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (param t)) (1 : ℝ)) : ℂ)
        = ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ)
              (fun q => (globalSimplexContLift L σ q : ℂ)) (param t)
            : (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
              (globalSimplexContLift L σ (param t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) param t
              : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (param t)) (1 : ℝ)) : ℂ) :=
      h_v
    have step3 : ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ)
              (fun q => (globalSimplexContLift L σ q : ℂ)) (param t)
            : (Fin 2 → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
              (globalSimplexContLift L σ (param t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) param t
              : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (param t)) (1 : ℝ)) : ℂ)
        = ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) F_param t
            : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (F_param t)) (1 : ℝ) : ℂ) := by
      have := h_chain_F
      exact_mod_cast this.symm
    exact step1.trans (step2.trans step3)
  -- Now prove: deriv F_param t = (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) F_param t) 1.
  -- This is `mfderiv_eq_fderiv` + standard fderiv_apply_one_eq_deriv.
  have h_mfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) F_param t = fderiv ℝ F_param t :=
    mfderiv_eq_fderiv (f := F_param) (x := t)
  rw [h_mfd]
  -- (fderiv ℝ F_param t) 1 = deriv F_param t.
  exact (fderiv_apply_one_eq_deriv (f := F_param) (x := t)).symm

/-! ## Per-face velocity integral identity -/

private lemma face_velocity_integral_eq_endpoint_diff
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (param : ℝ → (Fin 2 → ℝ))
    (h_param : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ param)
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (h_amb_eq : ∀ s ∈ Set.Ioo (0 : ℝ) 1, SmoothPath.ambient γ s = σ.toFun (param s)) :
    ∫ s in (0 : ℝ)..1, SmoothPath.velocity γ s
      = (globalSimplexContLift L σ (param 1) : ℂ)
        - (globalSimplexContLift L σ (param 0) : ℂ) := by
  set F_param : ℝ → ℂ := fun s : ℝ => (globalSimplexContLift L σ (param s) : ℂ)
  have h_F_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ F_param :=
    F_comp_param_contMDiff L σ param h_param
  have h_F_cont : Continuous F_param := h_F_smooth.continuous
  have h_F_cont_on : ContinuousOn F_param (Set.Icc 0 1) := h_F_cont.continuousOn
  have h_F_hasDeriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt F_param (SmoothPath.velocity γ t) t :=
    fun t ht => face_velocity_HasDerivAt_F_comp L σ param h_param γ h_amb_eq ht
  have h_vel_intInt : IntervalIntegrable (SmoothPath.velocity γ) volume 0 1 :=
    velocity_intervalIntegrable L γ
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := 1) zero_le_one h_F_cont_on h_F_hasDeriv h_vel_intInt

/-! ## The three faces -/

private lemma face2_velocity_integral
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    ∫ s in (0 : ℝ)..1, SmoothPath.velocity (Smooth2Simplex.face2 σ) s
      = (globalSimplexContLift L σ Smooth2Simplex.v1 : ℂ)
        - (globalSimplexContLift L σ Smooth2Simplex.v0 : ℂ) := by
  have h_param : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ Smooth2Simplex.face2Param :=
    Smooth2Simplex.contMDiff_face2Param
  have h_amb_eq : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      SmoothPath.ambient (Smooth2Simplex.face2 σ) s
        = σ.toFun (Smooth2Simplex.face2Param s) := by
    intro s hs
    have hs_uI : s ∈ unitInterval := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h := SmoothPath.ambient_eq_on_unitInterval (Smooth2Simplex.face2 σ)
      ⟨s, hs_uI⟩
    show SmoothPath.ambient (Smooth2Simplex.face2 σ) s
      = σ.toFun (Smooth2Simplex.face2Param s)
    rw [h]; rfl
  have h := face_velocity_integral_eq_endpoint_diff L σ Smooth2Simplex.face2Param h_param
    (Smooth2Simplex.face2 σ) h_amb_eq
  rw [h, Smooth2Simplex.face2Param_zero, Smooth2Simplex.face2Param_one]

private lemma face1_velocity_integral
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    ∫ s in (0 : ℝ)..1, SmoothPath.velocity (Smooth2Simplex.face1 σ) s
      = (globalSimplexContLift L σ Smooth2Simplex.v2 : ℂ)
        - (globalSimplexContLift L σ Smooth2Simplex.v0 : ℂ) := by
  have h_param : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ Smooth2Simplex.face1Param :=
    Smooth2Simplex.contMDiff_face1Param
  have h_amb_eq : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      SmoothPath.ambient (Smooth2Simplex.face1 σ) s
        = σ.toFun (Smooth2Simplex.face1Param s) := by
    intro s hs
    have hs_uI : s ∈ unitInterval := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h := SmoothPath.ambient_eq_on_unitInterval (Smooth2Simplex.face1 σ)
      ⟨s, hs_uI⟩
    show SmoothPath.ambient (Smooth2Simplex.face1 σ) s
      = σ.toFun (Smooth2Simplex.face1Param s)
    rw [h]; rfl
  have h := face_velocity_integral_eq_endpoint_diff L σ Smooth2Simplex.face1Param h_param
    (Smooth2Simplex.face1 σ) h_amb_eq
  rw [h, Smooth2Simplex.face1Param_zero, Smooth2Simplex.face1Param_one]

private lemma face0_velocity_integral
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    ∫ s in (0 : ℝ)..1, SmoothPath.velocity (Smooth2Simplex.face0 σ) s
      = (globalSimplexContLift L σ Smooth2Simplex.v2 : ℂ)
        - (globalSimplexContLift L σ Smooth2Simplex.v1 : ℂ) := by
  have h_param : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ Smooth2Simplex.face0Param :=
    Smooth2Simplex.contMDiff_face0Param
  have h_amb_eq : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      SmoothPath.ambient (Smooth2Simplex.face0 σ) s
        = σ.toFun (Smooth2Simplex.face0Param s) := by
    intro s hs
    have hs_uI : s ∈ unitInterval := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h := SmoothPath.ambient_eq_on_unitInterval (Smooth2Simplex.face0 σ)
      ⟨s, hs_uI⟩
    show SmoothPath.ambient (Smooth2Simplex.face0 σ) s
      = σ.toFun (Smooth2Simplex.face0Param s)
    rw [h]; rfl
  have h := face_velocity_integral_eq_endpoint_diff L σ Smooth2Simplex.face0Param h_param
    (Smooth2Simplex.face0 σ) h_amb_eq
  rw [h, Smooth2Simplex.face0Param_zero, Smooth2Simplex.face0Param_one]

/-! ## Telescoping vanishing -/

/-- **The boundary face velocity integral on any smooth 2-simplex
vanishes.** Telescoping the three endpoint differences:

```
(F(v2) - F(v1)) - (F(v2) - F(v0)) + (F(v1) - F(v0))
  = 0
```
-/
theorem boundary_face_velocity_integral_eq_zero
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    boundary_face_velocity_integral L σ = 0 := by
  unfold boundary_face_velocity_integral
  rw [face0_velocity_integral, face1_velocity_integral, face2_velocity_integral]
  ring

/-! ## Discharge of `RealImagDzInCanonicalClosed L` -/

/-- **The two remaining atomic Stokes inputs hold unconditionally on
`T_L = ℂ ⧸ L`.** -/
theorem realImagDzInCanonicalClosed_holds :
    RealImagDzInCanonicalClosed L :=
  realImagDzInCanonicalClosed_of_boundary_velocity_vanishing L
    (boundary_face_velocity_integral_eq_zero L)

/-- **`HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)` holds
unconditionally.** -/
theorem holomorphicComponentsCanonicalClosed_holds :
    HolomorphicComponentsCanonicalClosed (ℂ ⧸ L) :=
  holomorphicComponentsCanonicalClosed_of_realImagDz L
    (realImagDzInCanonicalClosed_holds L)

/-- **`HolomorphicStokesHypothesis (ℂ ⧸ L)` holds unconditionally.** -/
theorem holomorphicStokesHypothesis_holds :
    HolomorphicStokesHypothesis (ℂ ⧸ L) :=
  holomorphicStokesHypothesis_of_realImagDz L
    (realImagDzInCanonicalClosed_holds L)

end ComplexTorus

end JacobianChallenge

end
