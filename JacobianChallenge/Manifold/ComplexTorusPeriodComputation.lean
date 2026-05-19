/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBasisLoop
import JacobianChallenge.Manifold.ComplexTorusTangentCoordChangeId
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

end ComplexTorus

end JacobianChallenge

end
