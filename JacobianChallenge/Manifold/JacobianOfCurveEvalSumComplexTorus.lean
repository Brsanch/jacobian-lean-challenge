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

/-! ## Conditional `ofCurve_inj` on T_L

Under the two named classical hypotheses, `Jacobian.ofCurve P` is
injective on `ℂ ⧸ L`. The argument uses injectivity of
`evalSumPic0Equiv` (from `TLAbelConverseHypothesis`) to lift the
left-cancellation `Q₁ - P = Q₂ - P → Q₁ = Q₂` from `ℂ ⧸ L` back to
`Pic⁰ (ℂ ⧸ L)`.

This is a conditional discharge of Basic.lean Item 16 (`ofCurve_inj`)
for the special case `X = ℂ ⧸ L`. -/

/-- **Conditional `ofCurve_inj` on T_L.** Under both named classical
hypotheses, `Jacobian.ofCurve P : (ℂ ⧸ L) → Pic⁰ (ℂ ⧸ L)` is
injective. -/
theorem ofCurve_injective_complexTorus
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (P : ℂ ⧸ L) :
    Function.Injective
      (JacobianChallenge.Jacobian.ofCurve (X := ℂ ⧸ L) P) := by
  intro Q₁ Q₂ h
  have h_eval : evalSumPic0Equiv L hTL hConverse
        (JacobianChallenge.Jacobian.ofCurve (X := ℂ ⧸ L) P Q₁)
      = evalSumPic0Equiv L hTL hConverse
        (JacobianChallenge.Jacobian.ofCurve (X := ℂ ⧸ L) P Q₂) := by
    rw [h]
  rw [evalSumPic0Equiv_ofCurve L hTL hConverse,
      evalSumPic0Equiv_ofCurve L hTL hConverse] at h_eval
  -- h_eval : Q₁ - P = Q₂ - P
  exact sub_left_inj.mp h_eval

end ComplexTorus

end JacobianChallenge

end
