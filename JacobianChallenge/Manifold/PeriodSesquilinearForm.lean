/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.PeriodMatrix
import JacobianChallenge.Manifold.HodgeRiemannBridge

set_option linter.unusedSectionVars false

/-! # The period sesquilinear form

The matrix `periodMatrixForm pm J = pmᵀ · J.cast · pm.map star` at
entry `(i, j)` equals a **sesquilinear pairing** on `HolomorphicOneForm X`
when `pm` is itself realised as a period matrix `pm_{k, i} =
PeriodPairing data (cycleGens k) (basis_ω i)`.

That sesquilinear pairing is:

  `Q_sq J cycleGens data ω₀ ω₁
   := ∑ k l, J_{k,l} · PeriodPairing data (cycleGens k) ω₀
                    · star (PeriodPairing data (cycleGens l) ω₁)`,

ℂ-linear in `ω₀` and conjugate-linear in `ω₁` (the `star` flips
ℂ-linearity to conjugate-linearity). It is the sesquilinear analog of
`riemannBilinearPeriodForm` (which is bilinear, no conjugation).

The `HodgeRiemannBridgeHypothesis` at entry `(i, j)` then says

  `I · Q_sq J cycleGens data (basis_ω i) (basis_ω j) = H(basis_ω i, basis_ω j)`,

bridging a **sesquilinear pairing built from periods** (LHS) with the
**Hodge inner product** (RHS).

## What ships

* `periodSesquilinearForm` — the form `Q_sq`.
* `periodSesquilinearForm_eq_periodMatrixForm_apply` — pointwise identity
  on the basis: `Q_sq J cycleGens data (basis_ω i) (basis_ω j)
   = (periodMatrixForm pm J)_{i, j}` for `pm := periodMatrix data
   basis_ω cycleGens`.
* `hodgeRiemannBridgeHypothesis_iff_sesquilinear_identity` — bridge
  identity as a pairing identity on the basis.

## Significance

A more honest statement of the deep open Hodge-Riemann bridge
identity, exposing it as a sesquilinear pairing identity rather than a
matrix identity. This is the standard formulation in classical
algebraic geometry texts (e.g., Griffiths-Harris); the matrix form is
the same content recast as `g × g` complex matrices.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The period sesquilinear form.** -/
noncomputable def periodSesquilinearForm
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₀ ω₁ : HolomorphicOneForm X) : ℂ :=
  ∑ k : Fin (2 * JacobianChallenge.genus X),
    ∑ l : Fin (2 * JacobianChallenge.genus X),
      (J k l : ℂ) * PeriodPairing data (cycleGens k) ω₀
                  * star (PeriodPairing data (cycleGens l) ω₁)

/-- **`periodSesquilinearForm` reproduces `(periodMatrixForm pm J)_{i, j}`
on the basis.**

`Q_sq J cycleGens data (basis_ω i) (basis_ω j)
 = (periodMatrixForm (periodMatrix data basis_ω cycleGens) J)_{i, j}`. -/
theorem periodSesquilinearForm_eq_periodMatrixForm_apply
    {data : PeriodPairingData X}
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (i j : Fin (JacobianChallenge.genus X)) :
    periodSesquilinearForm cycleGens J (basis_ω i) (basis_ω j)
      = (periodMatrixForm (periodMatrix data basis_ω cycleGens) J) i j := by
  unfold periodSesquilinearForm periodMatrixForm
  -- RHS unfold: matrix product, then inner product.
  rw [Matrix.mul_apply]
  have h_rhs_inner :
      ∀ k_outer : Fin (2 * JacobianChallenge.genus X),
        ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)) i k_outer
          = ∑ l_inner,
              (periodMatrix data basis_ω cycleGens)ᵀ i l_inner
                * (J.map ((↑) : ℤ → ℂ)) l_inner k_outer := by
    intro k_outer
    exact Matrix.mul_apply ..
  simp_rw [h_rhs_inner, Finset.sum_mul]
  -- Both sides are ∑ ∑; swap RHS outer/inner.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  show (J l k : ℂ) * PeriodPairing data (cycleGens l) (basis_ω i)
        * star (PeriodPairing data (cycleGens k) (basis_ω j))
      = (periodMatrix data basis_ω cycleGens)ᵀ i l
          * (J.map ((↑) : ℤ → ℂ)) l k
          * (periodMatrix data basis_ω cycleGens).map star k j
  rw [Matrix.transpose_apply, periodMatrix_apply, Matrix.map_apply,
      Matrix.map_apply, periodMatrix_apply]
  ring

section BridgeAsSesquilinear

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

/-- **The Hodge-Riemann bridge identity as a sesquilinear pairing
identity.**

`HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H` is equivalent
to the per-pair pairing identity

  `∀ i j, I · Q_sq(basis_ω i, basis_ω j) = H(basis_ω i, basis_ω j)`. -/
theorem hodgeRiemannBridgeHypothesis_iff_sesquilinear_identity
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (H : HermitianOnHolomorphicOneForm X) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H ↔
      ∀ i j : Fin (JacobianChallenge.genus X),
        (Complex.I : ℂ) * periodSesquilinearForm cycleGens J
          (basis_ω i) (basis_ω j)
          = H.toFun (basis_ω i) (basis_ω j) := by
  unfold HodgeRiemannBridgeHypothesis
  constructor
  · intro h_matrix i j
    have h_entry := congrFun (congrFun h_matrix i) j
    -- Translate the matrix entry to the sesquilinear pairing.
    rw [show ((Complex.I : ℂ) •
          ((periodMatrix data basis_ω cycleGens)ᵀ
            * J.map ((↑) : ℤ → ℂ)
            * (periodMatrix data basis_ω cycleGens).map star)) i j
        = (Complex.I : ℂ) * (periodMatrixForm
            (periodMatrix data basis_ω cycleGens) J) i j from rfl] at h_entry
    rw [← periodSesquilinearForm_eq_periodMatrixForm_apply
          (data := data) basis_ω cycleGens J i j] at h_entry
    rw [HermitianOnHolomorphicOneForm.toMatrix_apply] at h_entry
    exact h_entry
  · intro h_pairing
    funext i j
    have h_pt := h_pairing i j
    rw [periodSesquilinearForm_eq_periodMatrixForm_apply
          (data := data) basis_ω cycleGens J i j] at h_pt
    rw [show ((Complex.I : ℂ) •
          ((periodMatrix data basis_ω cycleGens)ᵀ
            * J.map ((↑) : ℤ → ℂ)
            * (periodMatrix data basis_ω cycleGens).map star)) i j
        = (Complex.I : ℂ) * (periodMatrixForm
            (periodMatrix data basis_ω cycleGens) J) i j from rfl]
    rw [HermitianOnHolomorphicOneForm.toMatrix_apply]
    exact h_pt

end BridgeAsSesquilinear

end JacobianChallenge

end
