/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearImpliesLIGeneral
import Mathlib.Data.Matrix.Block

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # The Σ-matrix `[Π | star Π]` and its mulVec injectivity (chip 2B)

The general-g implication `RiemannBilinearRelations ⟹ ℝ-LI of period
vectors` factors through the `2g × 2g` Σ-matrix obtained by
column-concatenating the period matrix `pmat` and `star pmat`. This
file constructs Σ and proves that `Σ.mulVec` is injective on
`Fin g ⊕ Fin g → ℂ`, given:

* `pmatᵀ J pmat = 0` (first relation);
* `M := i pmatᵀ J pmat.map star` is invertible (consequence of second
  relation, chip 2A).

Note: we name the period matrix `pmat` rather than `Π` because Lean
reserves `Π` for Pi types.

The argument: suppose `Σ.mulVec y = 0`. View `y : Fin g ⊕ Fin g → ℂ`
as `(y₁, y₂)`. Block decomposition gives `pmat.mulVec y₁ + (star pmat).mulVec
y₂ = 0`. Apply `(pmatᵀ J).mulVec` to both sides:

* `(pmatᵀ J pmat).mulVec y₁ = 0` (first relation collapses);
* So `(pmatᵀ J star pmat).mulVec y₂ = 0` ⟹ `M.mulVec y₂ = 0`;
* `M` invertible ⟹ `y₂ = 0`.

Then `pmat.mulVec y₁ = 0`. To conclude `y₁ = 0`, take element-wise star:
`(star pmat).mulVec (star y₁) = 0`. Then `(0, star y₁)` satisfies the
same block hypothesis, so by the SAME right-half lemma, `star y₁ = 0`,
hence `y₁ = 0`.

The bridge to ℝ-LI of period vectors is in a follow-up chip.

## What this file ships

* `inner_unit_of_smul_I_unit` — small helper: `IsUnit (i • A) → IsUnit A`
  via `Matrix.det` and `IsUnit.mul_iff`.
* `periodSigmaBlock` — `Σ : Matrix (Fin (2 * g)) (Fin g ⊕ Fin g) ℂ` via
  `Sum.elim` on the column index.
* `periodSigmaBlock_mulVec` — block decomposition of `Σ.mulVec`.
* `right_half_eq_zero` — given block-sum vanishing, the right half is `0`.
* `left_half_eq_zero` — symmetric statement (via conjugation).
* `periodSigmaBlock_mulVec_injective_of_relations` — Σ's mulVec is
  injective given the bilinear relations.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Helper: stripping `i •` from `IsUnit` -/

/-- **Stripping `i •` from an `IsUnit` matrix witness.** Since `Complex.I`
is a unit in `ℂ`, `IsUnit (i • A) ↔ IsUnit A`. -/
lemma inner_unit_of_smul_I_unit {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (h : IsUnit ((Complex.I : ℂ) • A)) :
    IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  rw [Matrix.det_smul] at h
  exact (IsUnit.mul_iff.mp h).2

/-! ## Step 1: Build Σ via `Sum`-indexed columns -/

variable {g : ℕ}

/-- **`periodSigmaBlock pmat : Matrix (Fin (2g)) (Fin g ⊕ Fin g) ℂ`** — the
column-concatenation `[pmat | star pmat]` with column index in `Sum` form. -/
def periodSigmaBlock (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ) :
    Matrix (Fin (2 * g)) (Fin g ⊕ Fin g) ℂ :=
  fun i => Sum.elim (pmat i) (fun k => star (pmat i k))

@[simp] lemma periodSigmaBlock_inl
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ) (i : Fin (2 * g)) (k : Fin g) :
    periodSigmaBlock pmat i (Sum.inl k) = pmat i k := rfl

@[simp] lemma periodSigmaBlock_inr
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ) (i : Fin (2 * g)) (k : Fin g) :
    periodSigmaBlock pmat i (Sum.inr k) = star (pmat i k) := rfl

/-! ## Step 2: `Σ.mulVec` block decomposition -/

/-- **Block decomposition of `Σ.mulVec y`.** For `y : Fin g ⊕ Fin g → ℂ`,
`Σ.mulVec y = pmat.mulVec y_left + (star pmat).mulVec y_right`. -/
lemma periodSigmaBlock_mulVec
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (y : Fin g ⊕ Fin g → ℂ) :
    (periodSigmaBlock pmat) *ᵥ y
      = pmat *ᵥ (y ∘ Sum.inl) + (pmat.map star) *ᵥ (y ∘ Sum.inr) := by
  funext i
  show ∑ j, periodSigmaBlock pmat i j * y j
       = (pmat *ᵥ (y ∘ Sum.inl)) i + ((pmat.map star) *ᵥ (y ∘ Sum.inr)) i
  rw [Fintype.sum_sum_type]
  simp only [periodSigmaBlock_inl, periodSigmaBlock_inr]
  rfl

/-! ## Step 3: Right-half vanishing -/

/-- **Right-half vanishes.** Given the first relation `pmatᵀ J pmat = 0`
and `M := i pmatᵀ J pmat.map star` invertible, any solution
`pmat.mulVec y₁ + (star pmat).mulVec y₂ = 0` forces `y₂ = 0`. -/
theorem right_half_eq_zero
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star)))
    {y₁ y₂ : Fin g → ℂ}
    (hy : pmat *ᵥ y₁ + (pmat.map star) *ᵥ y₂ = 0) :
    y₂ = 0 := by
  -- Apply `(pmatᵀ * J.cast).mulVec` to both sides of `hy`.
  have hsum : (pmatᵀ * J.map ((↑) : ℤ → ℂ)) *ᵥ (pmat *ᵥ y₁)
              + (pmatᵀ * J.map ((↑) : ℤ → ℂ)) *ᵥ ((pmat.map star) *ᵥ y₂) = 0 := by
    rw [← mulVec_add, hy, mulVec_zero]
  -- First-relation collapse on the first term.
  have h1 : (pmatᵀ * J.map ((↑) : ℤ → ℂ)) *ᵥ (pmat *ᵥ y₁) = 0 := by
    rw [mulVec_mulVec, h_first, zero_mulVec]
  rw [h1, zero_add, mulVec_mulVec] at hsum
  -- Now: (pmatᵀ * J.cast * pmat.map star).mulVec y₂ = 0.
  -- Strip `i •` to get `IsUnit (pmatᵀ * J.cast * pmat.map star)`.
  have h_inner_unit := inner_unit_of_smul_I_unit h_M_unit
  -- Conclude y₂ = 0 from injectivity of mulVec.
  have h_inj := (mulVec_injective_iff_isUnit
    (A := pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star)).mpr h_inner_unit
  have : (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star) *ᵥ y₂
       = (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star) *ᵥ 0 := by
    rw [hsum, mulVec_zero]
  exact h_inj this

/-! ## Step 4: Reuse `right_half_eq_zero` via conjugation to get left-half -/

/-- **Left-half vanishes.** Given `pmat.mulVec y₁ = 0`, take element-wise
star to get `(star pmat).mulVec (star y₁) = 0`. Then `(0, star y₁)`
satisfies the right-half pivot hypothesis, forcing `star y₁ = 0` and
hence `y₁ = 0`. -/
theorem left_half_eq_zero
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star)))
    {y₁ : Fin g → ℂ}
    (hy₁ : pmat *ᵥ y₁ = 0) :
    y₁ = 0 := by
  -- Take element-wise star: (star pmat).mulVec (star y₁) = 0.
  have h_star : (pmat.map star) *ᵥ (star y₁) = 0 := by
    funext i
    show ∑ j, (pmat.map star) i j * (star y₁) j = (0 : Fin (2 * g) → ℂ) i
    show ∑ j, star (pmat i j) * star (y₁ j) = 0
    have h_pull : (∑ j, star (pmat i j) * star (y₁ j))
                = star (∑ j, pmat i j * y₁ j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [StarMul.star_mul]
      ring
    rw [h_pull]
    have : (∑ j, pmat i j * y₁ j) = (pmat *ᵥ y₁) i := rfl
    rw [this, hy₁]
    simp
  -- Apply right_half_eq_zero to (0, star y₁).
  have h_block_zero : pmat *ᵥ (0 : Fin g → ℂ) + (pmat.map star) *ᵥ (star y₁) = 0 := by
    rw [mulVec_zero, zero_add, h_star]
  have h_star_eq_zero :=
    right_half_eq_zero pmat J h_first h_M_unit (y₁ := 0) (y₂ := star y₁)
      h_block_zero
  -- star y₁ = 0 ⟹ y₁ = 0.
  funext i
  have : star (y₁ i) = 0 := by
    have := congr_fun h_star_eq_zero i
    simpa using this
  exact (star_eq_zero.mp this)

/-! ## Step 5: Σ's mulVec is injective -/

/-- **Σ-mulVec is injective.** Combining `right_half_eq_zero` (for the
right half) and `left_half_eq_zero` (for the left half, derived
symmetrically) gives full injectivity. -/
theorem periodSigmaBlock_mulVec_injective_of_relations
    (pmat : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (J : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (h_first : pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat = 0)
    (h_M_unit : IsUnit ((Complex.I : ℂ) •
      (pmatᵀ * J.map ((↑) : ℤ → ℂ) * pmat.map star))) :
    Function.Injective (periodSigmaBlock pmat).mulVec := by
  intro y₁ y₂ hy
  -- Set z := y₁ - y₂; reduce to z = 0 ⟹ y₁ = y₂.
  by_contra h_ne
  set z := y₁ - y₂ with hz_def
  have h_mv_z : (periodSigmaBlock pmat).mulVec z = 0 := by
    show (periodSigmaBlock pmat).mulVec (y₁ - y₂) = 0
    rw [mulVec_sub]
    exact sub_eq_zero.mpr hy
  have hz_ne : z ≠ 0 := fun h => h_ne (sub_eq_zero.mp h)
  -- Decompose z into halves.
  have h_decomp : pmat *ᵥ (z ∘ Sum.inl) + (pmat.map star) *ᵥ (z ∘ Sum.inr) = 0 := by
    rw [← periodSigmaBlock_mulVec]
    exact h_mv_z
  -- Right half vanishes.
  have h_right : z ∘ Sum.inr = 0 :=
    right_half_eq_zero pmat J h_first h_M_unit h_decomp
  -- With z ∘ Sum.inr = 0, decomposition gives pmat *ᵥ (z ∘ Sum.inl) = 0.
  have h_left_eq : pmat *ᵥ (z ∘ Sum.inl) = 0 := by
    have hh := h_decomp
    rw [h_right, mulVec_zero, add_zero] at hh
    exact hh
  -- Left half vanishes.
  have h_left : z ∘ Sum.inl = 0 :=
    left_half_eq_zero pmat J h_first h_M_unit h_left_eq
  -- Combine: z = 0.
  apply hz_ne
  funext j
  cases j with
  | inl k =>
    have : (z ∘ Sum.inl) k = 0 := by rw [h_left]; rfl
    exact this
  | inr k =>
    have : (z ∘ Sum.inr) k = 0 := by rw [h_right]; rfl
    exact this

end JacobianChallenge

end
