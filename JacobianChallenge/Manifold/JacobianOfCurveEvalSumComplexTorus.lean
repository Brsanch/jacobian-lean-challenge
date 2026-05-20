/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Jacobian
import JacobianChallenge.Manifold.Pic0EvalSumComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `evalSumPic0` and `Jacobian.ofCurve` on T_L

`JacobianChallenge.Jacobian X := Pic0 X`, so for `X = ℂ ⧸ L` the closed-
form Abel–Jacobi map `evalSumPic0` evaluates `Jacobian.ofCurve P Q` to
`Q − P` in `ℂ ⧸ L`. In particular at `P = 0` it returns `Q` exactly —
matching the classical AJ-on-zero-basepoint formula.

These identities specialize the general
`evalSumPic0_single_sub_single` to the canonical `ofCurve` constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`evalSumPic0` applied to `Jacobian.ofCurve P Q` returns `Q − P`.** -/
theorem evalSumPic0_ofCurve
    (hTL : TLDivSumHypothesis L) (P Q : ℂ ⧸ L) :
    evalSumPic0 L hTL (JacobianChallenge.Jacobian.ofCurve P Q) = Q - P := by
  classical
  -- Unfold `ofCurve` to `QuotientAddGroup.mk ⟨single Q - single P, …⟩`.
  show evalSumPic0 L hTL
      (QuotientAddGroup.mk
        (⟨Div.single Q - Div.single P,
          Div.single_sub_single_mem_Div0 P Q⟩ : Div0 (ℂ ⧸ L))) = Q - P
  rw [evalSumPic0_mk]
  -- The Div-level coercion of the Div0-subtype is the underlying divisor.
  show Div.evalSum ((Div.single Q - Div.single P : Div (ℂ ⧸ L))) = Q - P
  rw [Div.evalSum_single_sub_single]

/-- **`evalSumPic0_ofCurve` at the zero base point: identity on T_L.** -/
@[simp] theorem evalSumPic0_ofCurve_zero
    (hTL : TLDivSumHypothesis L) (Q : ℂ ⧸ L) :
    evalSumPic0 L hTL
        (JacobianChallenge.Jacobian.ofCurve (0 : ℂ ⧸ L) Q)
      = Q := by
  rw [evalSumPic0_ofCurve, sub_zero]

/-- **`evalSumPic0Equiv` applied to `Jacobian.ofCurve P Q` returns `Q − P`.** -/
theorem evalSumPic0Equiv_ofCurve
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (P Q : ℂ ⧸ L) :
    evalSumPic0Equiv L hTL hConverse
        (JacobianChallenge.Jacobian.ofCurve P Q)
      = Q - P :=
  evalSumPic0_ofCurve L hTL P Q

/-- **`evalSumPic0Equiv` at the zero base point: identity on T_L.** -/
@[simp] theorem evalSumPic0Equiv_ofCurve_zero
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (Q : ℂ ⧸ L) :
    evalSumPic0Equiv L hTL hConverse
        (JacobianChallenge.Jacobian.ofCurve (0 : ℂ ⧸ L) Q)
      = Q :=
  evalSumPic0_ofCurve_zero L hTL Q

end ComplexTorus

end JacobianChallenge

end
