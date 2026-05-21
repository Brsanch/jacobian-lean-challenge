/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrix
import JacobianChallenge.Manifold.CotangentWedgeVanishing

set_option linter.unusedSectionVars false

/-! # Abstract Riemann bilinear period form `Q`

`(periodMatrix data α cycleGens)ᵀ * J.cast * periodMatrix data α cycleGens`
is a `g × g` matrix whose entries are bilinear sums in the period
integrals. This file extracts the underlying bilinear form on
`HolomorphicOneForm X × HolomorphicOneForm X`:

  `Q J data cycleGens ω₀ ω₁ :=
    ∑ k, ∑ l, (J k l : ℂ) * PeriodPairing data (cycleGens k) ω₀
                           * PeriodPairing data (cycleGens l) ω₁`

so the periodMatrix off-diagonal entry `((periodMatrixᵀ · J · periodMatrix) i j)`
equals `Q J data cycleGens (α i) (α j)`. The Riemann first bilinear
relation is *precisely* the statement `Q ≡ 0` on `HolomorphicOneForm X
× HolomorphicOneForm X` — a single classical mathematical statement
factored out of the period-matrix presentation.

This chip establishes:

* `Q` is `ℂ`-linear in each argument (direct from
  `PeriodPairing_add_right` + `PeriodPairing_smul_right`).
* `Q` is antisymmetric when `J` is antisymmetric: `Q J ω₀ ω₁ = - Q J ω₁ ω₀`.
* Bridge: `(periodMatrixᵀ · J.cast · periodMatrix) i j = Q J (α i) (α j)`.

The chip-19/20 first-relation reductions (`pmatᵀ J pmat = 0`) factor
through this bridge: closing the classical content `Q ≡ 0` discharges
**every** strict-upper-triangular entry of `pmatᵀ · J · pmat`
simultaneously.

The substantive classical content `Q ≡ 0` will be the integration
identity `Q J ω₀ ω₁ = ∫_X ω₀ ∧ ω₁` composed with the pointwise type-(2,0)-
vanishing (`cotangent_wedge_pointwise_zero` from chip 5). Both bridges
are open in tree.

## What this file ships

* `riemannBilinearPeriodForm` — the abstract `Q` (a function, not yet
  bundled as a `BilinearForm`).
* `riemannBilinearPeriodForm_add_left` /
  `riemannBilinearPeriodForm_smul_left` /
  `riemannBilinearPeriodForm_add_right` /
  `riemannBilinearPeriodForm_smul_right` — bilinearity in each
  argument.
* `riemannBilinearPeriodForm_antisymm` — antisymmetry from
  antisymmetric `J`.
* `periodMatrix_form_eq_riemannBilinearPeriodForm` — the bridge to
  `(periodMatrixᵀ · J.cast · periodMatrix) i j = Q J (α i) (α j)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Abstract Riemann bilinear period form.**

`Q J data cycleGens ω₀ ω₁` is the bilinear sum that, evaluated at
basis 1-forms `α i, α j`, reproduces the `(i, j)` entry of
`periodMatrixᵀ * J.cast * periodMatrix`. The Riemann first bilinear
relation says this form is identically zero on holomorphic 1-forms. -/
noncomputable def riemannBilinearPeriodForm
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₀ ω₁ : HolomorphicOneForm X) : ℂ :=
  ∑ k : Fin (2 * JacobianChallenge.genus X),
    ∑ l : Fin (2 * JacobianChallenge.genus X),
      (J k l : ℂ) * PeriodPairing data (cycleGens k) ω₀
                  * PeriodPairing data (cycleGens l) ω₁

/-- **Additivity in the left argument.** -/
theorem riemannBilinearPeriodForm_add_left
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₀ ω₀' ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J (ω₀ + ω₀') ω₁
      = riemannBilinearPeriodForm cycleGens J ω₀ ω₁
          + riemannBilinearPeriodForm cycleGens J ω₀' ω₁ := by
  unfold riemannBilinearPeriodForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_add_right]
  ring

/-- **`ℂ`-linearity in the left argument.** -/
theorem riemannBilinearPeriodForm_smul_left
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (a : ℂ) (ω₀ ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J (a • ω₀) ω₁
      = a * riemannBilinearPeriodForm cycleGens J ω₀ ω₁ := by
  unfold riemannBilinearPeriodForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_smul_right, smul_eq_mul]
  ring

/-- **Additivity in the right argument.** -/
theorem riemannBilinearPeriodForm_add_right
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₀ ω₁ ω₁' : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J ω₀ (ω₁ + ω₁')
      = riemannBilinearPeriodForm cycleGens J ω₀ ω₁
          + riemannBilinearPeriodForm cycleGens J ω₀ ω₁' := by
  unfold riemannBilinearPeriodForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_add_right]
  ring

/-- **`ℂ`-linearity in the right argument.** -/
theorem riemannBilinearPeriodForm_smul_right
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (a : ℂ) (ω₀ ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J ω₀ (a • ω₁)
      = a * riemannBilinearPeriodForm cycleGens J ω₀ ω₁ := by
  unfold riemannBilinearPeriodForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [PeriodPairing_smul_right, smul_eq_mul]
  ring

/-- **Antisymmetry from antisymmetric `J`.**

If `Jᵀ = -J`, then `Q J ω₀ ω₁ = - Q J ω₁ ω₀`. Proof: swap the dummy
indices `k ↔ l` in the double sum on the RHS, then use `J_{l,k} = - J_{k,l}`. -/
theorem riemannBilinearPeriodForm_antisymm
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (ω₀ ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J ω₀ ω₁
      = - riemannBilinearPeriodForm cycleGens J ω₁ ω₀ := by
  unfold riemannBilinearPeriodForm
  -- J k l = - J l k pointwise.
  have hJ_swap : ∀ k l : Fin (2 * JacobianChallenge.genus X),
      (J k l : ℂ) = - (J l k : ℂ) := by
    intro k l
    have h : (Jᵀ) l k = (-J) l k := by rw [hJ]
    rw [Matrix.transpose_apply, Matrix.neg_apply] at h
    have h' : J k l = - J l k := h
    rw [show ((J k l : ℤ) : ℂ) = ((- J l k : ℤ) : ℂ) by rw [h']]
    push_cast
    ring
  -- Rewrite each entry of the LHS using J k l = - J l k, all in one shot.
  rw [show (∑ k : Fin (2 * JacobianChallenge.genus X),
            ∑ l : Fin (2 * JacobianChallenge.genus X),
              (J k l : ℂ) * PeriodPairing data (cycleGens k) ω₀
                * PeriodPairing data (cycleGens l) ω₁)
        = -(∑ k, ∑ l, (J l k : ℂ) * PeriodPairing data (cycleGens k) ω₀
              * PeriodPairing data (cycleGens l) ω₁) by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hJ_swap k l]
    ring]
  congr 1
  -- Goal: ∑ k ∑ l J(l,k) Pair(γ_k, ω₀) Pair(γ_l, ω₁) =
  --       ∑ k ∑ l J(k,l) Pair(γ_k, ω₁) Pair(γ_l, ω₀)
  -- Swap iteration order of sums on the LHS.
  rw [Finset.sum_comm]
  -- Goal: ∑ l ∑ k J(l,k) Pair(γ_k, ω₀) Pair(γ_l, ω₁) =
  --       ∑ k ∑ l J(k,l) Pair(γ_k, ω₁) Pair(γ_l, ω₀)
  -- Rename outer dummy l → k, inner dummy k → l (just a relabel of bound vars).
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  -- Goal: J(k,l) Pair(γ_l, ω₀) Pair(γ_k, ω₁) = J(k,l) Pair(γ_k, ω₁) Pair(γ_l, ω₀)
  ring

/-- **Bridge: the `(i, j)` entry of `periodMatrixᵀ · J.cast · periodMatrix`
equals `Q J (α i) (α j)`.**

This is the pure linear-algebra link between the matrix-presentation
of the first Riemann bilinear relation and the abstract bilinear form
`Q`. -/
theorem periodMatrix_form_eq_riemannBilinearPeriodForm
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (i j : Fin (JacobianChallenge.genus X)) :
    ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * periodMatrix data α cycleGens) i j
      = riemannBilinearPeriodForm cycleGens J (α i) (α j) := by
  unfold riemannBilinearPeriodForm
  -- Expand the outer matrix product entry (indexed by l).
  rw [Matrix.mul_apply]
  -- For each fixed l, expand the inner product (indexed by k).
  have h_inner : ∀ l : Fin (2 * JacobianChallenge.genus X),
      ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)) i l
          * periodMatrix data α cycleGens l j
        = ∑ k, (J k l : ℂ) * PeriodPairing data (cycleGens k) (α i)
                            * PeriodPairing data (cycleGens l) (α j) := by
    intro l
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.transpose_apply, periodMatrix_apply, periodMatrix_apply,
        Matrix.map_apply]
    ring
  rw [show (∑ l, ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)) i l
            * periodMatrix data α cycleGens l j)
        = (∑ l, ∑ k, (J k l : ℂ) * PeriodPairing data (cycleGens k) (α i)
                                  * PeriodPairing data (cycleGens l) (α j)) by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact h_inner l]
  -- Swap the iteration order: ∑ l ∑ k = ∑ k ∑ l.
  rw [Finset.sum_comm]

end JacobianChallenge

end
