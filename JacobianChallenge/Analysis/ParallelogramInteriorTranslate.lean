/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramCoordinates

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Interior translates: existence, uniqueness, and ball geometry

The last parallelogram prelims for the piece-5 assembly
(`HANDOFF_TLDIVSUM.md`):

* `coordS_add_int_combo` / `coordR_add_int_combo` — translating by
  `m₁·ω₁ + m₂·ω₂` shifts the Cramer coordinates by `(m₁, m₂)`;
* `eq_of_interior_translate` — **uniqueness**: two lattice translates
  of the same point cannot both be interior to `Π(a)` (their
  coordinates differ by integers inside `(0,1)`);
* `exists_interior_translate` — **existence**: if all translates'
  coordinates avoid `{0,1}` (regular position), some translate is
  interior (`m = −⌊coord⌋`);
* ball geometry: the four sides and all interior points lie in
  `ball a (‖ω₁‖ + ‖ω₂‖ + 1)`.

Together: for a regular-position base point, each lattice orbit meets
the open fundamental parallelogram exactly once, inside the ball that
the decomposition and the contour live in.

No `sorry`, no `axiom`. -/

noncomputable section

open Set

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-! ## Coordinate shift under lattice translation -/

lemma coordS_add_int_combo (hD : latticeCross ω₁ ω₂ ≠ 0)
    (z : ℂ) (k₁ k₂ : ℤ) :
    coordS a ω₁ ω₂ (z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂)
      = coordS a ω₁ ω₂ z + k₁ := by
  simp only [coordS]
  have hcross : latticeCross
      (z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂ - a) ω₂
      = latticeCross (z - a) ω₂ + (k₁ : ℝ) * latticeCross ω₁ ω₂ := by
    simp only [latticeCross, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  rw [hcross, add_div, mul_div_assoc, div_self hD, mul_one]

lemma coordR_add_int_combo (hD : latticeCross ω₁ ω₂ ≠ 0)
    (z : ℂ) (k₁ k₂ : ℤ) :
    coordR a ω₁ ω₂ (z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂)
      = coordR a ω₁ ω₂ z + k₂ := by
  simp only [coordR]
  have hcross : latticeCross ω₁
      (z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂ - a)
      = latticeCross ω₁ (z - a) + (k₂ : ℝ) * latticeCross ω₁ ω₂ := by
    simp only [latticeCross, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  rw [hcross, add_div, mul_div_assoc, div_self hD, mul_one]

/-! ## Uniqueness of the interior translate -/

/-- **Uniqueness**: a lattice translate of an interior point that is
itself interior is the point itself. -/
lemma eq_of_interior_translate (hD : latticeCross ω₁ ω₂ ≠ 0)
    {z : ℂ} (k₁ k₂ : ℤ)
    (hzs : coordS a ω₁ ω₂ z ∈ Ioo (0 : ℝ) 1)
    (hzr : coordR a ω₁ ω₂ z ∈ Ioo (0 : ℝ) 1)
    (hws : coordS a ω₁ ω₂ (z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂)
      ∈ Ioo (0 : ℝ) 1)
    (hwr : coordR a ω₁ ω₂ (z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂)
      ∈ Ioo (0 : ℝ) 1) :
    z + (k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂ = z := by
  have h1 := coordS_add_int_combo a ω₁ ω₂ hD z k₁ k₂
  have h2 := coordR_add_int_combo a ω₁ ω₂ hD z k₁ k₂
  obtain ⟨hzs0, hzs1⟩ := hzs
  obtain ⟨hzr0, hzr1⟩ := hzr
  obtain ⟨hws0, hws1⟩ := hws
  obtain ⟨hwr0, hwr1⟩ := hwr
  rw [h1] at hws0 hws1
  rw [h2] at hwr0 hwr1
  have hk₁ : k₁ = 0 := by
    have hlt : (-1 : ℝ) < (k₁ : ℝ) ∧ (k₁ : ℝ) < 1 :=
      ⟨by linarith, by linarith⟩
    have : (-1 : ℤ) < k₁ ∧ k₁ < 1 :=
      ⟨by exact_mod_cast hlt.1, by exact_mod_cast hlt.2⟩
    omega
  have hk₂ : k₂ = 0 := by
    have hlt : (-1 : ℝ) < (k₂ : ℝ) ∧ (k₂ : ℝ) < 1 :=
      ⟨by linarith, by linarith⟩
    have : (-1 : ℤ) < k₂ ∧ k₂ < 1 :=
      ⟨by exact_mod_cast hlt.1, by exact_mod_cast hlt.2⟩
    omega
  rw [hk₁, hk₂]
  push_cast
  ring

/-! ## Existence of the interior translate -/

/-- **Existence**: if every lattice translate of `z` has coordinates
avoiding `{0,1}` (regular position), then some translate is interior:
shift by `−⌊coord⌋`. -/
lemma exists_interior_translate (hD : latticeCross ω₁ ω₂ ≠ 0) {z : ℂ}
    (hne : ∀ m₁ m₂ : ℤ,
      coordS a ω₁ ω₂ (z + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 0 ∧
      coordS a ω₁ ω₂ (z + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 1 ∧
      coordR a ω₁ ω₂ (z + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 0 ∧
      coordR a ω₁ ω₂ (z + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 1) :
    ∃ m₁ m₂ : ℤ,
      coordS a ω₁ ω₂ (z + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂)
        ∈ Ioo (0 : ℝ) 1 ∧
      coordR a ω₁ ω₂ (z + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂)
        ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨-⌊coordS a ω₁ ω₂ z⌋, -⌊coordR a ω₁ ω₂ z⌋, ?_, ?_⟩
  · have hval : coordS a ω₁ ω₂
        (z + ((-⌊coordS a ω₁ ω₂ z⌋ : ℤ) : ℂ) * ω₁
          + ((-⌊coordR a ω₁ ω₂ z⌋ : ℤ) : ℂ) * ω₂)
        = coordS a ω₁ ω₂ z - ⌊coordS a ω₁ ω₂ z⌋ := by
      rw [coordS_add_int_combo a ω₁ ω₂ hD]
      push_cast
      ring
    have hne0 := (hne (-⌊coordS a ω₁ ω₂ z⌋) (-⌊coordR a ω₁ ω₂ z⌋)).1
    rw [hval] at hne0 ⊢
    constructor
    · have hfl := Int.floor_le (coordS a ω₁ ω₂ z)
      exact lt_of_le_of_ne (by linarith) (Ne.symm hne0)
    · have hfl := Int.lt_floor_add_one (coordS a ω₁ ω₂ z)
      linarith
  · have hval : coordR a ω₁ ω₂
        (z + ((-⌊coordS a ω₁ ω₂ z⌋ : ℤ) : ℂ) * ω₁
          + ((-⌊coordR a ω₁ ω₂ z⌋ : ℤ) : ℂ) * ω₂)
        = coordR a ω₁ ω₂ z - ⌊coordR a ω₁ ω₂ z⌋ := by
      rw [coordR_add_int_combo a ω₁ ω₂ hD]
      push_cast
      ring
    have hne0 := (hne (-⌊coordS a ω₁ ω₂ z⌋) (-⌊coordR a ω₁ ω₂ z⌋)).2.2.1
    rw [hval] at hne0 ⊢
    constructor
    · have hfl := Int.floor_le (coordR a ω₁ ω₂ z)
      exact lt_of_le_of_ne (by linarith) (Ne.symm hne0)
    · have hfl := Int.lt_floor_add_one (coordR a ω₁ ω₂ z)
      linarith

/-! ## Ball geometry: sides and interior points -/

lemma side₀_mem_ball : ∀ t ∈ Icc (0 : ℝ) 1,
    side₀ a ω₁ ω₂ t ∈ Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [side₀, Metric.mem_ball, dist_eq_norm]
  have h1 : a + t • ω₁ - a = t • ω₁ := by ring
  rw [h1, Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg ω₁, norm_nonneg ω₂]

lemma side₁_mem_ball : ∀ t ∈ Icc (0 : ℝ) 1,
    side₁ a ω₁ ω₂ t ∈ Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [side₁, Metric.mem_ball, dist_eq_norm]
  have h1 : a + ω₁ + t • ω₂ - a = ω₁ + t • ω₂ := by ring
  rw [h1]
  calc ‖ω₁ + t • ω₂‖ ≤ ‖ω₁‖ + ‖t • ω₂‖ := norm_add_le _ _
    _ = ‖ω₁‖ + t * ‖ω₂‖ := by
        rw [Complex.real_smul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg ht0]
    _ < ‖ω₁‖ + ‖ω₂‖ + 1 := by nlinarith [norm_nonneg ω₂]

lemma side₂_mem_ball : ∀ t ∈ Icc (0 : ℝ) 1,
    side₂ a ω₁ ω₂ t ∈ Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 : side₂ a ω₁ ω₂ t - a = (1 - t) • ω₁ + ω₂ := by
    rw [side₂]
    module
  rw [h1]
  calc ‖(1 - t) • ω₁ + ω₂‖ ≤ ‖(1 - t) • ω₁‖ + ‖ω₂‖ := norm_add_le _ _
    _ = (1 - t) * ‖ω₁‖ + ‖ω₂‖ := by
        rw [Complex.real_smul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    _ < ‖ω₁‖ + ‖ω₂‖ + 1 := by nlinarith [norm_nonneg ω₁]

lemma side₃_mem_ball : ∀ t ∈ Icc (0 : ℝ) 1,
    side₃ a ω₁ ω₂ t ∈ Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 : side₃ a ω₁ ω₂ t - a = (1 - t) • ω₂ := by
    rw [side₃]
    module
  rw [h1, Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  nlinarith [norm_nonneg ω₁, norm_nonneg ω₂]

/-- Interior points (coordinates in `(0,1)²`) lie in the standard
ball. -/
lemma mem_ball_of_coord_interior (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hs : coordS a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1)
    (hr : coordR a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1) :
    x ∈ Metric.ball a (‖ω₁‖ + ‖ω₂‖ + 1) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  have hx := interiorPt_coords a ω₁ ω₂ hD x
  rw [Metric.mem_ball, dist_eq_norm, ← hx, interiorPt]
  have h1 : a + coordS a ω₁ ω₂ x • ω₁ + coordR a ω₁ ω₂ x • ω₂ - a
      = coordS a ω₁ ω₂ x • ω₁ + coordR a ω₁ ω₂ x • ω₂ := by
    ring
  rw [h1]
  calc ‖coordS a ω₁ ω₂ x • ω₁ + coordR a ω₁ ω₂ x • ω₂‖
      ≤ ‖coordS a ω₁ ω₂ x • ω₁‖ + ‖coordR a ω₁ ω₂ x • ω₂‖ :=
        norm_add_le _ _
    _ = coordS a ω₁ ω₂ x * ‖ω₁‖ + coordR a ω₁ ω₂ x * ‖ω₂‖ := by
        rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hs0, abs_of_pos hr0]
    _ < ‖ω₁‖ + ‖ω₂‖ + 1 := by
        nlinarith [norm_nonneg ω₁, norm_nonneg ω₂]

end ParallelogramWinding

end JacobianChallenge

end
