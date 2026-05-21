/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodSigmaInvertibility
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fin.SuccPred

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # From `Σ.mulVec` injectivity to ℝ-LI of period vectors (chip 2C)

This file closes the general-g implication

  `RiemannBilinearRelations data α cycleGens
     ⟹ LinearIndependent ℝ (fun i => periodVector data α (cycleGens i))`

The argument:

1. The `2g × (Fin g ⊕ Fin g)` `periodSigmaBlock` matrix has injective
   `mulVec` (chip 2B).
2. Reindex columns via the canonical `Fin g ⊕ Fin g ≃ Fin (2g)`
   to get a square `2g × 2g` matrix `periodSigma` whose `mulVec` is
   still injective.
3. For a square matrix over a field, injective `mulVec` ⟺ `IsUnit`.
4. `IsUnit periodSigma` ⟹ rows of `periodSigma` are ℂ-LI.
5. Bridge to ℂ-LI of rows of `periodSigmaBlock` via the index equiv.
6. Real combination `∑ a_i • pmat.row i = 0` ⟹ (conjugation, real
   coefs commute with star) `∑ (a_i : ℂ) • periodSigmaBlock.row i = 0`.
   By ℂ-LI, `(a_i : ℂ) = 0`, hence `a_i = 0`.

## What this file ships

* `periodSigmaBlockIndexEquiv` — the `Fin g ⊕ Fin g ≃ Fin (2g)` bridge.
* `periodSigma` — square reindexed Σ.
* `periodSigma_mulVec_injective_of_relations` — square Σ's mulVec is injective.
* `periodSigma_isUnit_of_relations` — square Σ is `IsUnit`.
* `linearIndependent_periodSigmaBlock_row_of_relations` — rows of
  `periodSigmaBlock` are ℂ-LI.
* `linearIndependent_periodMatrix_row_of_relations` — main result:
  ℝ-LI of `pmat`'s rows from `RiemannBilinearRelations`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

variable {g : ℕ}

/-! ## Step 1: Reindex Σ to a square matrix -/

/-- **Canonical reindex equivalence** `Fin g ⊕ Fin g ≃ Fin (2 * g)`. -/
def periodSigmaBlockIndexEquiv (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- **Square Σ matrix.** -/
def periodSigma (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ) :
    Matrix (Fin (2 * g)) (Fin (2 * g)) ℂ :=
  (periodSigmaBlock pmat).submatrix id (periodSigmaBlockIndexEquiv g).symm

lemma periodSigma_apply
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i j : Fin (2 * g)) :
    periodSigma pmat i j
      = periodSigmaBlock pmat i ((periodSigmaBlockIndexEquiv g).symm j) := rfl

/-! ## Step 2: `periodSigma.mulVec` injectivity from `periodSigmaBlock`'s -/

lemma periodSigma_mulVec
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (y : Fin (2 * g) → ℂ) :
    (periodSigma pmat) *ᵥ y
      = (periodSigmaBlock pmat) *ᵥ (y ∘ periodSigmaBlockIndexEquiv g) := by
  funext i
  show ∑ j, periodSigma pmat i j * y j
       = ∑ j', periodSigmaBlock pmat i j' * (y ∘ periodSigmaBlockIndexEquiv g) j'
  rw [show (∑ j, periodSigma pmat i j * y j)
        = ∑ j' : Fin g ⊕ Fin g, periodSigma pmat i (periodSigmaBlockIndexEquiv g j')
            * y (periodSigmaBlockIndexEquiv g j') from
        (Equiv.sum_comp (periodSigmaBlockIndexEquiv g) _).symm]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [periodSigma_apply, Equiv.symm_apply_apply]
  rfl

theorem periodSigma_mulVec_injective_of_relations
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star))) :
    Function.Injective (periodSigma pmat).mulVec := by
  intro y₁ y₂ hy
  have h_block :
      (periodSigmaBlock pmat) *ᵥ (y₁ ∘ periodSigmaBlockIndexEquiv g)
        = (periodSigmaBlock pmat) *ᵥ (y₂ ∘ periodSigmaBlockIndexEquiv g) := by
    rw [← periodSigma_mulVec, ← periodSigma_mulVec]; exact hy
  have h_block_inj :=
    periodSigmaBlock_mulVec_injective_of_relations pmat J h_first h_M_unit
  have h_pre := h_block_inj h_block
  funext i
  have : (y₁ ∘ periodSigmaBlockIndexEquiv g)
            ((periodSigmaBlockIndexEquiv g).symm i)
        = (y₂ ∘ periodSigmaBlockIndexEquiv g)
            ((periodSigmaBlockIndexEquiv g).symm i) := by
    rw [h_pre]
  simpa [Function.comp_apply, Equiv.apply_symm_apply] using this

/-! ## Step 3: `IsUnit periodSigma` -/

theorem periodSigma_isUnit_of_relations
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star))) :
    IsUnit (periodSigma pmat) :=
  mulVec_injective_iff_isUnit.mp
    (periodSigma_mulVec_injective_of_relations pmat J h_first h_M_unit)

/-! ## Step 4: ℂ-LI of `periodSigmaBlock` rows -/

theorem linearIndependent_periodSigmaBlock_row_of_relations
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star))) :
    LinearIndependent ℂ (fun i => periodSigmaBlock pmat i) := by
  have h_sq :=
    linearIndependent_rows_iff_isUnit.mpr
      (periodSigma_isUnit_of_relations pmat J h_first h_M_unit)
  rw [Fintype.linearIndependent_iff] at h_sq ⊢
  intro c hc
  apply h_sq c
  funext k
  -- hc : ∑ i, c i • periodSigmaBlock pmat i = 0 (function value).
  -- Apply at j := (e g).symm k:
  have hc_at := congr_fun hc ((periodSigmaBlockIndexEquiv g).symm k)
  -- LHS in Fintype.linearIndependent_iff sums use the elaborated mul.
  -- hc_at : (∑ i, c i • periodSigmaBlock pmat i) ((e g).symm k) = 0.
  -- Goal: (∑ i, c i • (periodSigma pmat).row i) k = 0.
  -- Both reduce to ∑ i, c i * (periodSigmaBlock pmat i ((e g).symm k)).
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc_at ⊢
  -- After simp: hc_at : ∑ i, c i * periodSigmaBlock pmat i ((e g).symm k) = 0.
  -- Goal:        ∑ i, c i * (periodSigma pmat).row i k = 0.
  -- (periodSigma pmat).row i k = periodSigma pmat i k = periodSigmaBlock pmat i ((e g).symm k).
  convert hc_at using 2

/-! ## Step 5: Real LI of period-matrix rows -/

/-- **ℝ-LI of `pmat.row` from ℂ-LI of `periodSigmaBlock.row`.** -/
theorem linearIndependent_periodMatrix_row_of_relations
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star))) :
    LinearIndependent ℝ (fun i : Fin (2 * g) => (pmat i : Fin g → ℂ)) := by
  have h_block_LI :=
    linearIndependent_periodSigmaBlock_row_of_relations pmat J h_first h_M_unit
  rw [Fintype.linearIndependent_iff] at h_block_LI ⊢
  intro a ha
  intro i₀
  -- a : Fin (2g) → ℝ, ha : ∑ i, a i • (fun j => pmat i j) = 0 in Fin g → ℂ.
  -- Get (Complex.ofReal ∘ a) i₀ = 0 from h_block_LI.
  have h_cast_zero : (Complex.ofReal ∘ a) i₀ = 0 := by
    apply h_block_LI (Complex.ofReal ∘ a)
    funext j
    -- Cases on j ∈ Fin g ⊕ Fin g.
    cases j with
    | inl k =>
      have ha_k := congr_fun ha k
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at ha_k
      -- ha_k : ∑ i, a i • pmat i k = 0 (a : ℝ-action on ℂ-valued).
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
                 periodSigmaBlock_inl, Function.comp_apply]
      -- Goal: ∑ i, (a i : ℂ) * pmat i k = 0.
      rw [show ∑ i, (a i : ℂ) * pmat i k = ∑ i, a i • pmat i k from
          Finset.sum_congr rfl (fun i _ => by rw [Complex.real_smul])]
      exact ha_k
    | inr k =>
      have ha_k := congr_fun ha k
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at ha_k
      -- ha_k : ∑ i, a i • pmat i k = 0 (a : ℝ-action on ℂ).
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
                 periodSigmaBlock_inr, Function.comp_apply]
      -- Goal: ∑ i, (a i : ℂ) * star (pmat i k) = 0.
      -- Convert ha_k to (a i : ℂ) form.
      have ha_k' : ∑ i, (a i : ℂ) * pmat i k = 0 := by
        rw [show ∑ i, (a i : ℂ) * pmat i k = ∑ i, a i • pmat i k from
            Finset.sum_congr rfl (fun i _ => by rw [Complex.real_smul])]
        exact ha_k
      -- Take star.
      have ha_k_star : star (∑ i, (a i : ℂ) * pmat i k) = 0 := by
        rw [ha_k']; simp
      -- Bridge ∑ (a i : ℂ) * star (pmat i k) = star (∑ (a i : ℂ) * pmat i k).
      rw [show (∑ i, (a i : ℂ) * star (pmat i k))
          = star (∑ i, (a i : ℂ) * pmat i k) from ?_]
      · exact ha_k_star
      · rw [star_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        -- (a i : ℂ) * star (pmat i k) = star ((a i : ℂ) * pmat i k).
        rw [StarMul.star_mul]
        rw [show star ((a i : ℂ)) = (a i : ℂ) from by simp [Complex.conj_ofReal]]
        ring
  -- h_cast_zero : (a i₀ : ℂ) = 0.
  simp only [Function.comp_apply] at h_cast_zero
  -- Cast (a i₀ : ℂ) = 0 to a i₀ = 0.
  exact_mod_cast h_cast_zero

/-! ## Step 6: Composite from `RiemannBilinearRelations` to ℝ-LI of period vectors -/

/-- **Main result.** Given `RiemannBilinearRelations data α cycleGens`,
the 2g period vectors `periodVector data α (cycleGens i)` are ℝ-linearly
independent in `Fin g → ℂ`. -/
theorem RiemannBilinear2ImpliesRealLI_of_relations
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h_rel : RiemannBilinearRelations data basis_ω cycleGens) :
    RiemannBilinear2ImpliesRealLI data basis_ω cycleGens := by
  obtain ⟨J, h_first, h_second⟩ := h_rel
  -- Unfold the relations into the matrix form.
  have h_first_mat : (periodMatrix data basis_ω cycleGens)ᵀ
                      * J.map ((↑) : ℤ → ℂ)
                      * periodMatrix data basis_ω cycleGens = 0 :=
    h_first
  have h_M_unit : IsUnit ((Complex.I : ℂ) •
    ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
      * (periodMatrix data basis_ω cycleGens).map star)) :=
    isUnit_riemannBilinear2_matrix h_second
  -- Conclude ℝ-LI of period vectors.
  unfold RiemannBilinear2ImpliesRealLI
  -- Note: `periodVector data α γ = fun j => PeriodPairing data γ (α j) = fun j => periodMatrix _ γ j`.
  -- More precisely: periodVector data basis_ω (cycleGens i) j = periodMatrix data basis_ω cycleGens i j.
  exact linearIndependent_periodMatrix_row_of_relations
    (periodMatrix data basis_ω cycleGens) J h_first_mat h_M_unit

end JacobianChallenge

end
