/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import JacobianChallenge.Analysis.L2OnManifold

/-! # `L²` inner product for inner-product-space-valued integrands

This file extends the foundational `L²` substrate in
`Analysis/L2OnManifold.lean` (ZZ128) with a *real* `L²` inner-product
functional on functions valued in a real inner-product space `F`.

The construction is deliberately measure-theoretic and does not depend
on the manifold structure: it works for any measurable space `α` with
a measure `μ` and any real inner-product space `F`. This is the layer
that subsequent chips can specialize:

* `α = M`, `μ =` compact-manifold finite measure, `F = ℝ` →
  scalar `L²(M)` inner product;
* `α = ℝⁿ`, `μ = volume.restrict φ.target`, `F = EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ` →
  chart-local `L²` inner product on Fréchet-derivative fields, the
  Sobolev–`H¹` Dirichlet form ingredient;
* `α = M`, `F =` cotangent fibre at a point, after the future
  cotangent-inner-product chip lands → the smooth `1`-form `L²`
  inner product targeted by the Hodge cluster.

## Contents

* `L2Inner μ s t` — the real number `∫ x, ⟪s x, t x⟫_ℝ ∂μ`.
* `L2Inner_zero_left` / `L2Inner_zero_right` — vanishing on zero.
* `L2Inner_symm` — symmetry `⟪s,t⟫ = ⟪t,s⟫`.
* `L2Inner_add_left` / `L2Inner_add_right` — additivity in each slot
  under joint `IsL2`.
* `L2Inner_smul_left` / `L2Inner_smul_right` — `ℝ`-bilinearity.
* `L2Inner_self_nonneg` — positive semidefiniteness `0 ≤ ⟪s,s⟫`.
* `L2Inner_self_eq_integral_normSq` — self-pairing identity
  `⟪s,s⟫ = ∫ x, ‖s x‖^2 ∂μ`, bridging to `L2NormSq`.

## Implementation notes

* We work with the *Bochner* integral `∫` (not `∫⁻`) because the inner
  product `⟪·,·⟫_ℝ` is real-valued and can be negative; `L2NormSq`
  (which is unsigned) keeps its existing `ℝ≥0∞` form.
* Additivity-in-each-slot needs joint integrability of the pointwise
  inner product. That is supplied here by `integrable_inner_of_isL2`,
  obtained by passing through `MemLp.toLp` and applying mathlib's
  `L2.integrable_inner`, then transferring via a.e.-equality.
* No new mathlib imports beyond `L2Space` (already used in
  `L2OnManifold`) and `InnerProductSpace.Basic` (already transitively
  pulled in by mathlib's `L2Space`, but listed explicitly here for
  documentation).
-/

noncomputable section

namespace JacobianChallenge

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The real `L²` inner product of two `F`-valued functions against a
measure `μ`:

`L2Inner μ s t = ∫ x, ⟪s x, t x⟫_ℝ ∂μ`. -/
def L2Inner (μ : Measure α) (s t : α → F) : ℝ :=
  ∫ x, @inner ℝ F _ (s x) (t x) ∂μ

/-- Joint integrability of the pointwise inner product of two `L²`
functions. We pass to `Lp` representatives, invoke mathlib's
`L2.integrable_inner`, and transfer back via a.e.-equality. -/
lemma integrable_inner_of_isL2 {μ : Measure α} {s t : α → F}
    (hs : IsL2 μ s) (ht : IsL2 μ t) :
    Integrable (fun x => @inner ℝ F _ (s x) (t x)) μ := by
  -- `s` and `t` agree a.e. with their `Lp` representatives.
  have hs_ae : (fun x => hs.toLp s x) =ᵐ[μ] s := hs.coeFn_toLp
  have ht_ae : (fun x => ht.toLp t x) =ᵐ[μ] t := ht.coeFn_toLp
  -- The inner product of the `Lp` representatives is integrable.
  have hint :
      Integrable
        (fun x => @inner ℝ F _ (hs.toLp s x) (ht.toLp t x)) μ :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hs.toLp s) (ht.toLp t)
  -- Pointwise inner products agree a.e..
  have h_ae :
      (fun x => @inner ℝ F _ (hs.toLp s x) (ht.toLp t x))
        =ᵐ[μ]
      (fun x => @inner ℝ F _ (s x) (t x)) := by
    filter_upwards [hs_ae, ht_ae] with x hxs hxt
    rw [hxs, hxt]
  exact hint.congr h_ae

@[simp]
lemma L2Inner_zero_left (μ : Measure α) (t : α → F) :
    L2Inner μ (fun _ => (0 : F)) t = 0 := by
  unfold L2Inner
  simp

@[simp]
lemma L2Inner_zero_right (μ : Measure α) (s : α → F) :
    L2Inner μ s (fun _ => (0 : F)) = 0 := by
  unfold L2Inner
  simp

/-- Symmetry of the real `L²` inner product. -/
lemma L2Inner_symm (μ : Measure α) (s t : α → F) :
    L2Inner μ s t = L2Inner μ t s := by
  unfold L2Inner
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact (real_inner_comm (t x) (s x))

/-- Additivity in the left slot of the `L²` inner product, under
joint `IsL2` of all three functions involved. -/
lemma L2Inner_add_left {μ : Measure α} {s₁ s₂ t : α → F}
    (hs₁ : IsL2 μ s₁) (hs₂ : IsL2 μ s₂) (ht : IsL2 μ t) :
    L2Inner μ (fun x => s₁ x + s₂ x) t
      = L2Inner μ s₁ t + L2Inner μ s₂ t := by
  unfold L2Inner
  have hi₁ : Integrable (fun x => @inner ℝ F _ (s₁ x) (t x)) μ :=
    integrable_inner_of_isL2 hs₁ ht
  have hi₂ : Integrable (fun x => @inner ℝ F _ (s₂ x) (t x)) μ :=
    integrable_inner_of_isL2 hs₂ ht
  have hpt : ∀ x,
      @inner ℝ F _ (s₁ x + s₂ x) (t x)
        = @inner ℝ F _ (s₁ x) (t x) + @inner ℝ F _ (s₂ x) (t x) := by
    intro x; exact inner_add_left _ _ _
  calc
    ∫ x, @inner ℝ F _ (s₁ x + s₂ x) (t x) ∂μ
        = ∫ x, @inner ℝ F _ (s₁ x) (t x) + @inner ℝ F _ (s₂ x) (t x) ∂μ := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => hpt x)
      _ = (∫ x, @inner ℝ F _ (s₁ x) (t x) ∂μ)
          + ∫ x, @inner ℝ F _ (s₂ x) (t x) ∂μ := by
          exact integral_add hi₁ hi₂

/-- Additivity in the right slot of the `L²` inner product, under
joint `IsL2` of all three functions involved. -/
lemma L2Inner_add_right {μ : Measure α} {s t₁ t₂ : α → F}
    (hs : IsL2 μ s) (ht₁ : IsL2 μ t₁) (ht₂ : IsL2 μ t₂) :
    L2Inner μ s (fun x => t₁ x + t₂ x)
      = L2Inner μ s t₁ + L2Inner μ s t₂ := by
  -- Reduce to the left version via symmetry.
  have h := L2Inner_add_left (μ := μ) (t := s) ht₁ ht₂ hs
  -- h : L2Inner μ (t₁+t₂) s = L2Inner μ t₁ s + L2Inner μ t₂ s
  rw [L2Inner_symm μ s (fun x => t₁ x + t₂ x),
      L2Inner_symm μ s t₁, L2Inner_symm μ s t₂]
  exact h

/-- Real scalar pulls out of the left slot of the `L²` inner product. -/
lemma L2Inner_smul_left (μ : Measure α) (c : ℝ) (s t : α → F) :
    L2Inner μ (fun x => c • s x) t = c * L2Inner μ s t := by
  unfold L2Inner
  have hpt : ∀ x,
      @inner ℝ F _ (c • s x) (t x) = c * @inner ℝ F _ (s x) (t x) := by
    intro x
    have := inner_smul_left (𝕜 := ℝ) (x := s x) (y := t x) (r := c)
    -- `inner_smul_left` gives `⟪c•x, y⟫ = conj c * ⟪x,y⟫`; over ℝ,
    -- `conj = id`.
    simpa using this
  calc
    ∫ x, @inner ℝ F _ (c • s x) (t x) ∂μ
        = ∫ x, c * @inner ℝ F _ (s x) (t x) ∂μ := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => hpt x)
      _ = c * ∫ x, @inner ℝ F _ (s x) (t x) ∂μ := by
          exact integral_const_mul c _

/-- Real scalar pulls out of the right slot of the `L²` inner product. -/
lemma L2Inner_smul_right (μ : Measure α) (c : ℝ) (s t : α → F) :
    L2Inner μ s (fun x => c • t x) = c * L2Inner μ s t := by
  -- Reduce to the left version via symmetry.
  rw [L2Inner_symm μ s (fun x => c • t x), L2Inner_smul_left μ c t s,
      L2Inner_symm μ t s]

/-- The `L²` self-inner product equals the Bochner integral of the
pointwise squared norm. This is the bridge to `L2NormSq` and the
positive-semidefiniteness witness. -/
lemma L2Inner_self_eq_integral_normSq (μ : Measure α) (s : α → F) :
    L2Inner μ s s = ∫ x, ‖s x‖ ^ 2 ∂μ := by
  unfold L2Inner
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact real_inner_self_eq_norm_sq (s x)

/-- The `L²` self-inner product is nonnegative: a positive-
semidefiniteness witness. -/
lemma L2Inner_self_nonneg (μ : Measure α) (s : α → F) :
    0 ≤ L2Inner μ s s := by
  rw [L2Inner_self_eq_integral_normSq]
  refine integral_nonneg ?_
  intro x
  exact sq_nonneg _

end JacobianChallenge

end
