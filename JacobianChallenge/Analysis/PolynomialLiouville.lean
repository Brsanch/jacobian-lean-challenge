/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Polynomial-growth Liouville theorem (degree ≤ 1)

An entire function `ℂ → ℂ` with linear growth at infinity is an affine
function: `f z = f 0 + (deriv f 0) * z`.

This generalises mathlib's basic Liouville theorem
(`Differentiable.exists_const_forall_eq_of_bounded`, where the conclusion
is "constant" for bounded entire functions) to the "polynomial of degree
≤ 1" conclusion under linear-growth hypothesis.

## Main results

* `JacobianChallenge.Complex.deriv_norm_le_of_growth_linear` — for entire
  `f : ℂ → ℂ` with linear growth `‖f z‖ ≤ C ‖z‖` for `‖z‖ ≥ R₀`, the
  derivative `deriv f` is bounded by `C` everywhere. Proven via the
  Cauchy first-derivative estimate (mathlib's
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`).
* `JacobianChallenge.Complex.polynomial_liouville_linear` — the headline
  statement: entire + linear growth ⇒ `f z = f 0 + deriv f 0 * z`. Proven
  by applying basic Liouville to `deriv f` (constant), then applying
  constancy from zero derivative to `f - (deriv f 0) * z`.

No `sorry`, no `axiom`.
-/

open Filter Set Bornology Function
open scoped Topology

namespace JacobianChallenge.Complex

/-- **Sphere bound from linear growth.** If `‖f z‖ ≤ C · ‖z‖` for
`‖z‖ ≥ R₀` and `R ≥ R₀ + ‖c‖`, then on the sphere of radius `R` around
`c`, `‖f z‖ ≤ C * (‖c‖ + R)`. -/
private lemma sphere_bound_of_growth_linear
    {f : ℂ → ℂ} {C R₀ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖)
    (c : ℂ) (R : ℝ) (hR : R₀ + ‖c‖ ≤ R) :
    ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C * (‖c‖ + R) := by
  intro z hz
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  -- `hz : ‖z - c‖ = R`.
  -- Reverse triangle: `R = ‖z - c‖ = ‖z + (-c)‖ ≤ ‖z‖ + ‖c‖`, so `‖z‖ ≥ R - ‖c‖`.
  have h_tri_lb : ‖z - c‖ ≤ ‖z‖ + ‖c‖ := by
    have eqv : z - c = z + (-c) := by ring
    rw [eqv]
    calc ‖z + (-c)‖ ≤ ‖z‖ + ‖-c‖ := norm_add_le _ _
      _ = ‖z‖ + ‖c‖ := by rw [norm_neg]
  have h_z_lb : R - ‖c‖ ≤ ‖z‖ := by rw [hz] at h_tri_lb; linarith
  -- Triangle: `‖z‖ = ‖c + (z - c)‖ ≤ ‖c‖ + R`.
  have h_tri_ub : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
    have eqv : z = c + (z - c) := by ring
    nth_rewrite 1 [eqv]
    exact norm_add_le _ _
  have h_z_ub : ‖z‖ ≤ ‖c‖ + R := by rw [hz] at h_tri_ub; exact h_tri_ub
  have h_z_ge_R₀ : R₀ ≤ ‖z‖ := by linarith
  have h_bd_z : ‖f z‖ ≤ C * ‖z‖ := hbd z h_z_ge_R₀
  calc ‖f z‖ ≤ C * ‖z‖ := h_bd_z
    _ ≤ C * (‖c‖ + R) := mul_le_mul_of_nonneg_left h_z_ub hC

/-- **The derivative of an entire function with linear growth is
bounded.** For entire `f : ℂ → ℂ` with `‖f z‖ ≤ C · ‖z‖` whenever
`R₀ ≤ ‖z‖`, every value `deriv f c` is bounded by `C`. Cauchy's first
derivative estimate `‖deriv f c‖ ≤ sup_{sphere c R} ‖f‖ / R`, combined
with the sphere bound `≤ C(‖c‖ + R)`, gives `‖deriv f c‖ ≤ C‖c‖/R + C`;
sending `R → ∞` yields `‖deriv f c‖ ≤ C`. -/
theorem deriv_norm_le_of_growth_linear
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C R₀ : ℝ} (hC : 0 ≤ C) (hR₀ : 0 ≤ R₀)
    (hbd : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖)
    (c : ℂ) :
    ‖deriv f c‖ ≤ C := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  -- `ha : C < a`. Goal: `‖deriv f c‖ ≤ a`.
  -- Set `δ := a - C > 0`. Choose `R ≥ R₀ + ‖c‖` and `R ≥ C·‖c‖/δ + 1`.
  have hδ_pos : 0 < a - C := sub_pos.mpr ha
  set R : ℝ := R₀ + ‖c‖ + C * ‖c‖ / (a - C) + 1 with hR_def
  have hC_norm_ratio_nn : 0 ≤ C * ‖c‖ / (a - C) :=
    div_nonneg (mul_nonneg hC (norm_nonneg _)) hδ_pos.le
  have hR_pos : 0 < R := by
    rw [hR_def]; linarith [norm_nonneg c]
  have hR_ge : R₀ + ‖c‖ ≤ R := by rw [hR_def]; linarith
  -- Sphere bound on `f`.
  have h_sphere : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C * (‖c‖ + R) :=
    sphere_bound_of_growth_linear hC hbd c R hR_ge
  -- Cauchy's first-derivative estimate.
  have h_cauchy : ‖deriv f c‖ ≤ C * (‖c‖ + R) / R :=
    _root_.Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (f := f) hR_pos hf.diffContOnCl h_sphere
  -- Split `C(‖c‖+R)/R = C·‖c‖/R + C`.
  have h_split : C * (‖c‖ + R) / R = C * ‖c‖ / R + C := by
    rw [mul_add, add_div]
    congr 1
    field_simp
  -- Bound `C·‖c‖/R ≤ a - C`.
  have h_delta_bd : C * ‖c‖ / R ≤ a - C := by
    rw [div_le_iff₀ hR_pos]
    -- want: `C * ‖c‖ ≤ (a - C) * R`
    -- `R ≥ C*‖c‖/(a-C) + 1`, so `(a-C)*R ≥ (a-C)*(C*‖c‖/(a-C) + 1) = C*‖c‖ + (a-C)`.
    have h_R_lb : C * ‖c‖ / (a - C) + 1 ≤ R := by
      rw [hR_def]; linarith [norm_nonneg c]
    have h_eR_lb : (a - C) * (C * ‖c‖ / (a - C) + 1) ≤ (a - C) * R :=
      mul_le_mul_of_nonneg_left h_R_lb hδ_pos.le
    have h_simplify : (a - C) * (C * ‖c‖ / (a - C) + 1) = C * ‖c‖ + (a - C) := by
      field_simp
    linarith
  -- Combine: `‖deriv f c‖ ≤ C*(‖c‖+R)/R = C*‖c‖/R + C ≤ (a-C) + C = a`.
  calc ‖deriv f c‖ ≤ C * (‖c‖ + R) / R := h_cauchy
    _ = C * ‖c‖ / R + C := h_split
    _ ≤ (a - C) + C := by linarith
    _ = a := by ring

/-- **Polynomial-growth Liouville theorem.** An entire function
`f : ℂ → ℂ` with linear growth `‖f z‖ ≤ C · ‖z‖` for `‖z‖ ≥ R₀` is an
affine function: `f z = f 0 + (deriv f 0) * z`.

Proof: by `deriv_norm_le_of_growth_linear`, `deriv f` is bounded by `C`.
Since `deriv f` is differentiable (the derivative of an entire function
is entire), basic Liouville says `deriv f` is constant, equal to
`deriv f 0`. Then `f - (deriv f 0) * id` has zero derivative
everywhere; by constancy from `is_const_of_deriv_eq_zero`, it equals
`f 0`. -/
theorem polynomial_liouville_linear
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C R₀ : ℝ} (hC : 0 ≤ C) (hR₀ : 0 ≤ R₀)
    (hbd : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖)
    (z : ℂ) :
    f z = f 0 + deriv f 0 * z := by
  -- 1. `deriv f` is bounded by `C` everywhere.
  have h_deriv_bd : ∀ c : ℂ, ‖deriv f c‖ ≤ C :=
    deriv_norm_le_of_growth_linear hf hC hR₀ hbd
  -- 2. `deriv f` is differentiable (deriv of entire is entire).
  have h_deriv_diff : Differentiable ℂ (deriv f) :=
    fun w => ((hf.analyticAt w).deriv).differentiableAt
  -- 3. `deriv f` has bounded range.
  have h_deriv_bdd : IsBounded (range (deriv f)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro y ⟨w, rfl⟩
    exact h_deriv_bd w
  -- 4. By basic Liouville, `deriv f` is constant.
  have h_deriv_const : ∀ w : ℂ, deriv f w = deriv f 0 :=
    fun w => h_deriv_diff.apply_eq_apply_of_bounded h_deriv_bdd w 0
  -- 5. Define `g(w) := f w - (deriv f 0) * w` and show its derivative is 0.
  set g : ℂ → ℂ := fun w => f w - deriv f 0 * w with hg_def
  have hg_diff : Differentiable ℂ g := by
    rw [hg_def]
    exact hf.sub ((differentiable_const _).mul differentiable_id)
  have h_deriv_g : ∀ w : ℂ, deriv g w = 0 := by
    intro w
    -- Compute the derivative of `g` at `w` via `HasDerivAt`.
    have h_f_dwa : HasDerivAt f (deriv f w) w := hf.differentiableAt.hasDerivAt
    have h_lin_dwa : HasDerivAt (fun y : ℂ => deriv f 0 * y) (deriv f 0) w := by
      have h_id : HasDerivAt (id : ℂ → ℂ) 1 w := hasDerivAt_id w
      have := h_id.const_mul (deriv f 0)
      simpa using this
    have h_g_dwa : HasDerivAt g (deriv f w - deriv f 0) w := h_f_dwa.sub h_lin_dwa
    have h_deriv_g_step : deriv g w = deriv f w - deriv f 0 := h_g_dwa.deriv
    rw [h_deriv_g_step, h_deriv_const w, sub_self]
  -- 6. By constancy from zero derivative, `g z = g 0`.
  have h_g_const : g z = g 0 := is_const_of_deriv_eq_zero hg_diff h_deriv_g z 0
  -- 7. `g 0 = f 0`, `g z = f z - (deriv f 0) * z`. Conclude.
  have h_g_zero : g 0 = f 0 := by
    show f 0 - deriv f 0 * 0 = f 0
    ring
  have h_g_z : g z = f z - deriv f 0 * z := rfl
  -- `f z - (deriv f 0) * z = f 0`, so `f z = f 0 + (deriv f 0) * z`.
  have h_eq : f z - deriv f 0 * z = f 0 := by rw [← h_g_z, h_g_const, h_g_zero]
  linear_combination h_eq

end JacobianChallenge.Complex
