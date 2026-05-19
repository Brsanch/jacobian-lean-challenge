/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBasisLoop
import JacobianChallenge.Manifold.ComplexTorusTangentCoordChangeId
import JacobianChallenge.Manifold.ComplexTorusMkQMfderiv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-! # mfderiv computations toward the torus period `∫_{γ_lam} dz = lam`

Foundational computations:

* `mfderiv_ofReal_mul_const`: the smooth map `t ↦ (t : ℂ) * lam` from
  `ℝ` to `ℂ` has `mfderiv` at any `t` mapping `1 ↦ lam`.

* `mfderiv_mkQ`: the quotient projection `L.mkQ : ℂ → ℂ ⧸ L` has
  `mfderiv` at any `p` mapping `v ↦ v` (identity ℝ-linear map), via
  the local chart `(localChart L _ p).symm` which has `mkQ` as its
  inverse on `ball p (r/2)`.

* `mfderiv_torusBasisLoop_ambient_witness`: combining the two via
  chain rule, the explicit ambient `fun t => mkQ ((t : ℂ) * lam)` of
  `torusBasisLoop lam` has `mfderiv` at any `t` mapping `1 ↦ lam`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

/-! ## mfderiv of `t ↦ (t : ℂ) * lam` -/

/-- The map `t ↦ (t : ℂ) * lam` is ℝ-linear in `t` (via the canonical
embedding `Complex.ofRealCLM`), so its derivative is multiplication
by `lam`, applied to `1` gives `lam`. -/
lemma fderiv_ofReal_mul_const (lam : ℂ) (t : ℝ) :
    fderiv ℝ (fun u : ℝ => (u : ℂ) * lam) t
      = ContinuousLinearMap.smulRight (Complex.ofRealCLM) lam := by
  have h_ofReal : Differentiable ℝ ((↑) : ℝ → ℂ) :=
    Complex.ofRealCLM.differentiable
  have h_eq : ∀ u : ℝ, (u : ℂ) * lam = (Complex.ofRealCLM.smulRight lam) u := by
    intro u
    rfl
  rw [show (fun u : ℝ => (u : ℂ) * lam)
        = (Complex.ofRealCLM.smulRight lam : ℝ →L[ℝ] ℂ) from by
        funext u; exact (h_eq u).symm]
  exact (Complex.ofRealCLM.smulRight lam : ℝ →L[ℝ] ℂ).fderiv

/-- The `mfderiv` of `t ↦ (t : ℂ) * lam` is the same as `fderiv` (since
both source and target use the trivial real models). -/
lemma mfderiv_ofReal_mul_const_apply_one (lam : ℂ) (t : ℝ) :
    (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (fun u : ℝ => (u : ℂ) * lam) t
        : ℝ →L[ℝ] ℂ) (1 : ℝ) = lam := by
  -- For trivial models, mfderiv = fderiv.
  have h_eq : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) (fun u : ℝ => (u : ℂ) * lam) t
      : ℝ →L[ℝ] ℂ) = fderiv ℝ (fun u : ℝ => (u : ℂ) * lam) t :=
    mfderiv_eq_fderiv (f := fun u : ℝ => (u : ℂ) * lam) (x := t)
  rw [h_eq, fderiv_ofReal_mul_const]
  -- (smulRight ofRealCLM lam) 1 = ofRealCLM 1 • lam = (1 : ℂ) * lam = lam.
  show (ContinuousLinearMap.smulRight (Complex.ofRealCLM) lam) (1 : ℝ) = lam
  rw [ContinuousLinearMap.smulRight_apply]
  change ((Complex.ofRealCLM (1 : ℝ) : ℂ)) • lam = lam
  rw [show (Complex.ofRealCLM (1 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) from rfl,
      Complex.ofReal_one, one_smul]

/-! ## Velocity of `t ↦ mkQ ((t : ℂ) * lam) : ℝ → ℂ ⧸ L` -/

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- The smooth witness function `f t = mkQ ((t : ℂ) * lam)` is the
ambient lift of `torusBasisLoop lam hlam` on `ℝ`. -/
noncomputable def torusBasisAmbient (lam : ℂ) : ℝ → ℂ ⧸ L :=
  fun t : ℝ => L.mkQ ((t : ℂ) * lam)

/-- `torusBasisAmbient L lam` is `ContMDiff` everywhere. -/
lemma torusBasisAmbient_contMDiff (lam : ℂ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (torusBasisAmbient L lam) := by
  have h_mul : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun t : ℝ => (t : ℂ) * lam) := by
    have h_ofReal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((↑) : ℝ → ℂ) :=
      Complex.ofRealCLM.contDiff
    exact (h_ofReal.mul contDiff_const).contMDiff
  have h_mkQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ (L.mkQ : ℂ → ℂ ⧸ L) :=
    mkQ_contMDiff_real L ∞
  exact h_mkQ.comp h_mul

/-- **Velocity of `torusBasisAmbient L lam` at any `t : ℝ`, applied
to `1`, equals `lam` (in `ℂ` via the TangentSpace identification).**
Chain rule combining `mfderiv_mkQ_apply` and
`mfderiv_ofReal_mul_const_apply_one`. -/
theorem mfderiv_torusBasisAmbient_apply_one (lam : ℂ) (t : ℝ) :
    (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (torusBasisAmbient L lam) t
        : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (torusBasisAmbient L lam t)) (1 : ℝ))
        : ℂ) = lam := by
  -- Chain rule: mfderiv (mkQ ∘ g) t = (mfderiv mkQ (g t)) ∘L (mfderiv g t).
  -- Then apply at 1.
  have h_g_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun u : ℝ => (u : ℂ) * lam) t := by
    rw [mdifferentiableAt_iff_differentiableAt]
    have : Differentiable ℝ (fun u : ℝ => (u : ℂ) * lam) := by
      exact (Complex.ofRealCLM.differentiable).mul_const lam
    exact this.differentiableAt
  have h_mkQ_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (L.mkQ : ℂ → ℂ ⧸ L) ((t : ℂ) * lam) :=
    (mkQ_contMDiff_real L 1).contMDiffAt.mdifferentiableAt one_ne_zero
  -- mfderiv (mkQ ∘ (·*lam)) t = (mfderiv mkQ ((t:ℂ)*lam)) ∘L (mfderiv (·*lam) t).
  show ((((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      ((L.mkQ : ℂ → ℂ ⧸ L) ∘ (fun u : ℝ => (u : ℂ) * lam)) t) (1 : ℝ))
        : ℂ)) = lam
  rw [mfderiv_comp t h_mkQ_diff h_g_diff]
  -- Goal: ((mfderiv mkQ ((t:ℂ)*lam)).comp (mfderiv (·*lam) t)) 1 = lam.
  -- This equals (mfderiv mkQ ((t:ℂ)*lam)) ((mfderiv (·*lam) t) 1) by .comp definition.
  -- Then (mfderiv (·*lam) t) 1 = lam, and (mfderiv mkQ ((t:ℂ)*lam)) lam = lam.
  -- Combine all in one step via a `change` followed by chain.
  change ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) ((t : ℂ) * lam))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun u : ℝ => (u : ℂ) * lam) t : ℝ →L[ℝ] ℂ)
        (1 : ℝ))
      : ℂ) = lam
  rw [mfderiv_ofReal_mul_const_apply_one lam t]
  exact mfderiv_mkQ_apply L ((t : ℂ) * lam) lam

end ComplexTorus

end JacobianChallenge

end
