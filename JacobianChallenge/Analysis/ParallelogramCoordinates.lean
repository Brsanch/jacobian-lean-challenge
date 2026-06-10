/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramWindingEval
import JacobianChallenge.Analysis.ParallelogramWindingExterior

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Parallelogram coordinates and the complete winding dichotomy

Piece-3 item (iv) of the forward-Abel contour argument
(`HANDOFF_TLDIVSUM.md`): the affine coordinate map `z ↦ (s, r)` with
`z = a + s·ω₁ + r·ω₂` via explicit Cramer formulas
(`coordS`/`coordR`), its inversion (`interiorPt_coords`), the
coordinate values on the four sides of `∂Π(a; ω₁, ω₂)` (all in
`[0,1]`), and the **complete winding dichotomy** in coordinates:

* `boundaryIntegral_inv_sub_of_coord_interior` — coordinates in
  `(0,1)²` ⟹ `∮_{∂Π} (z−x)⁻¹ = ±2πi` (sign of the orientation);
* `boundaryIntegral_inv_sub_of_coord_exterior` — either coordinate
  outside `[0,1]` ⟹ `∮_{∂Π} (z−x)⁻¹ = 0`, via a coordinate
  separating functional (`sepFunctional`) and the rotated-log
  primitive (`boundaryIntegral_inv_sub_exterior`).

Together with `boundaryIntegral_eq_sum_winding`
(`ParallelogramResidue.lean`) this evaluates the parallelogram residue
formula: interior poles contribute `±2πi·coeff`, exterior poles
contribute nothing.

No `sorry`, no `axiom`. -/

noncomputable section

open Set

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-! ## The Cramer coordinates -/

/-- The `ω₁`-coordinate of `z` relative to the base point `a`:
`s` in `z = a + s·ω₁ + r·ω₂`. -/
def coordS (z : ℂ) : ℝ :=
  latticeCross (z - a) ω₂ / latticeCross ω₁ ω₂

/-- The `ω₂`-coordinate of `z` relative to the base point `a`:
`r` in `z = a + s·ω₁ + r·ω₂`. -/
def coordR (z : ℂ) : ℝ :=
  latticeCross ω₁ (z - a) / latticeCross ω₁ ω₂

lemma latticeCross_smul_add_smul_right (s r : ℝ) :
    latticeCross (s • ω₁ + r • ω₂) ω₂ = s * latticeCross ω₁ ω₂ := by
  simp only [latticeCross, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma latticeCross_smul_add_smul_left (s r : ℝ) :
    latticeCross ω₁ (s • ω₁ + r • ω₂) = r * latticeCross ω₁ ω₂ := by
  simp only [latticeCross, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma coordS_interiorPt (hD : latticeCross ω₁ ω₂ ≠ 0) (s r : ℝ) :
    coordS a ω₁ ω₂ (interiorPt a ω₁ ω₂ s r) = s := by
  have h : interiorPt a ω₁ ω₂ s r - a = s • ω₁ + r • ω₂ := by
    rw [interiorPt]
    module
  rw [coordS, h, latticeCross_smul_add_smul_right, mul_div_assoc,
    div_self hD, mul_one]

lemma coordR_interiorPt (hD : latticeCross ω₁ ω₂ ≠ 0) (s r : ℝ) :
    coordR a ω₁ ω₂ (interiorPt a ω₁ ω₂ s r) = r := by
  have h : interiorPt a ω₁ ω₂ s r - a = s • ω₁ + r • ω₂ := by
    rw [interiorPt]
    module
  rw [coordR, h, latticeCross_smul_add_smul_left, mul_div_assoc,
    div_self hD, mul_one]

/-- **Cramer's rule in cleared form**: the cross-coordinate
combination of `ω₁, ω₂` reproduces `D·(z − a)`. -/
lemma cramer_identity (z : ℂ) :
    (latticeCross (z - a) ω₂ : ℂ) * ω₁ + (latticeCross ω₁ (z - a) : ℂ) * ω₂
      = (latticeCross ω₁ ω₂ : ℂ) * (z - a) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, latticeCross, Complex.sub_re, Complex.sub_im,
      zero_mul, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, latticeCross, Complex.sub_re, Complex.sub_im,
      zero_mul, add_zero]
    ring

/-- **Reconstruction**: every point is the interior-point expression of
its own coordinates. -/
lemma interiorPt_coords (hD : latticeCross ω₁ ω₂ ≠ 0) (z : ℂ) :
    interiorPt a ω₁ ω₂ (coordS a ω₁ ω₂ z) (coordR a ω₁ ω₂ z) = z := by
  have hD' : (latticeCross ω₁ ω₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  have hkey := cramer_identity a ω₁ ω₂ z
  rw [interiorPt, coordS, coordR, Complex.real_smul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_div]
  field_simp
  linear_combination hkey

/-! ## The four sides in interior-point form and their coordinates -/

lemma side₀_eq_interiorPt (t : ℝ) :
    side₀ a ω₁ ω₂ t = interiorPt a ω₁ ω₂ t 0 := by
  rw [side₀, interiorPt]
  module

lemma side₁_eq_interiorPt (t : ℝ) :
    side₁ a ω₁ ω₂ t = interiorPt a ω₁ ω₂ 1 t := by
  rw [side₁, interiorPt]
  module

lemma side₂_eq_interiorPt (t : ℝ) :
    side₂ a ω₁ ω₂ t = interiorPt a ω₁ ω₂ (1 - t) 1 := by
  rw [side₂, interiorPt]
  module

lemma side₃_eq_interiorPt (t : ℝ) :
    side₃ a ω₁ ω₂ t = interiorPt a ω₁ ω₂ 0 (1 - t) := by
  rw [side₃, interiorPt]
  module

lemma coordS_side₀ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordS a ω₁ ω₂ (side₀ a ω₁ ω₂ t) = t := by
  rw [side₀_eq_interiorPt, coordS_interiorPt a ω₁ ω₂ hD]

lemma coordR_side₀ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordR a ω₁ ω₂ (side₀ a ω₁ ω₂ t) = 0 := by
  rw [side₀_eq_interiorPt, coordR_interiorPt a ω₁ ω₂ hD]

lemma coordS_side₁ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordS a ω₁ ω₂ (side₁ a ω₁ ω₂ t) = 1 := by
  rw [side₁_eq_interiorPt, coordS_interiorPt a ω₁ ω₂ hD]

lemma coordR_side₁ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordR a ω₁ ω₂ (side₁ a ω₁ ω₂ t) = t := by
  rw [side₁_eq_interiorPt, coordR_interiorPt a ω₁ ω₂ hD]

lemma coordS_side₂ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordS a ω₁ ω₂ (side₂ a ω₁ ω₂ t) = 1 - t := by
  rw [side₂_eq_interiorPt, coordS_interiorPt a ω₁ ω₂ hD]

lemma coordR_side₂ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordR a ω₁ ω₂ (side₂ a ω₁ ω₂ t) = 1 := by
  rw [side₂_eq_interiorPt, coordR_interiorPt a ω₁ ω₂ hD]

lemma coordS_side₃ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordS a ω₁ ω₂ (side₃ a ω₁ ω₂ t) = 0 := by
  rw [side₃_eq_interiorPt, coordS_interiorPt a ω₁ ω₂ hD]

lemma coordR_side₃ (hD : latticeCross ω₁ ω₂ ≠ 0) (t : ℝ) :
    coordR a ω₁ ω₂ (side₃ a ω₁ ω₂ t) = 1 - t := by
  rw [side₃_eq_interiorPt, coordR_interiorPt a ω₁ ω₂ hD]

/-! ## The coordinate separating functional -/

/-- The separating functional `I·conj β`: its real pairing with `u`
computes the cross product, `Re(u · (I·conj β)) = latticeCross u β`. -/
def sepFunctional (β : ℂ) : ℂ := Complex.I * (starRingEnd ℂ) β

lemma re_mul_sepFunctional (u β : ℂ) :
    (u * sepFunctional β).re = latticeCross u β := by
  simp only [sepFunctional, latticeCross, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The `s`-coordinate difference formula. -/
lemma re_sub_mul_sepFunctional_coordS (hD : latticeCross ω₁ ω₂ ≠ 0)
    (x w : ℂ) :
    ((w - x) * sepFunctional ω₂).re
      = latticeCross ω₁ ω₂ * (coordS a ω₁ ω₂ w - coordS a ω₁ ω₂ x) := by
  rw [re_mul_sepFunctional, coordS, coordS]
  field_simp
  simp only [latticeCross, Complex.sub_re, Complex.sub_im]
  ring

/-- The `r`-coordinate difference formula. -/
lemma re_sub_mul_neg_sepFunctional_coordR (hD : latticeCross ω₁ ω₂ ≠ 0)
    (x w : ℂ) :
    ((w - x) * (-sepFunctional ω₁)).re
      = latticeCross ω₁ ω₂ * (coordR a ω₁ ω₂ w - coordR a ω₁ ω₂ x) := by
  rw [mul_neg, Complex.neg_re, re_mul_sepFunctional, coordR, coordR]
  field_simp
  simp only [latticeCross, Complex.sub_re, Complex.sub_im]
  ring

/-! ## Exterior vanishing in coordinates -/

/-- **Exterior core**: if a coordinate function `φ` paired by `c` via
`Re((w−x)·c) = D·(φ w − φ x)` takes values in `[0,1]` on all four sides
and `φ x < 0`, the winding around `x` vanishes. -/
lemma exterior_core (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (φ : ℂ → ℝ) (c : ℂ)
    (hre : ∀ w : ℂ, ((w - x) * c).re
      = latticeCross ω₁ ω₂ * (φ w - φ x))
    (hs₀ : ∀ t ∈ Icc (0 : ℝ) 1, φ (side₀ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1)
    (hs₁ : ∀ t ∈ Icc (0 : ℝ) 1, φ (side₁ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1)
    (hs₂ : ∀ t ∈ Icc (0 : ℝ) 1, φ (side₂ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1)
    (hs₃ : ∀ t ∈ Icc (0 : ℝ) 1, φ (side₃ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1)
    (hx : φ x < 0) :
    boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹) = 0 := by
  set σ : ℝ := if 0 < latticeCross ω₁ ω₂ then 1 else -1 with hσ_def
  have hσD : 0 < σ * latticeCross ω₁ ω₂ := by
    rcases lt_trichotomy (latticeCross ω₁ ω₂) 0 with h | h | h
    · rw [hσ_def, if_neg (by linarith)]
      nlinarith
    · exact absurd h hD
    · rw [hσ_def, if_pos h]
      nlinarith
  have hpt : ∀ w : ℂ, φ w ∈ Icc (0 : ℝ) 1 →
      0 < ((w - x) * ((σ : ℂ) * c)).re := by
    intro w hw
    have h1 : ((w - x) * ((σ : ℂ) * c)).re = σ * ((w - x) * c).re := by
      rw [show (w - x) * ((σ : ℂ) * c) = (σ : ℂ) * ((w - x) * c) by ring,
        Complex.mul_re]
      simp
    have h2 : 0 < φ w - φ x := by
      have := (Set.mem_Icc.mp hw).1
      linarith
    rw [h1, hre w]
    calc (0 : ℝ)
        < (σ * latticeCross ω₁ ω₂) * (φ w - φ x) := mul_pos hσD h2
      _ = σ * (latticeCross ω₁ ω₂ * (φ w - φ x)) := by ring
  exact boundaryIntegral_inv_sub_exterior a ω₁ ω₂ x ((σ : ℂ) * c)
    (fun t ht => hpt _ (hs₀ t ht)) (fun t ht => hpt _ (hs₁ t ht))
    (fun t ht => hpt _ (hs₂ t ht)) (fun t ht => hpt _ (hs₃ t ht))

/-- **Exterior winding vanishes in coordinates**: if either Cramer
coordinate of `x` lies outside `[0,1]`, the parallelogram boundary
integral of `(z − x)⁻¹` is zero. -/
theorem boundaryIntegral_inv_sub_of_coord_exterior
    (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hx : coordS a ω₁ ω₂ x ∉ Icc (0 : ℝ) 1
      ∨ coordR a ω₁ ω₂ x ∉ Icc (0 : ℝ) 1) :
    boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹) = 0 := by
  rcases hx with hx | hx
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · -- `coordS x < 0`
      exact exterior_core a ω₁ ω₂ hD (coordS a ω₁ ω₂) (sepFunctional ω₂)
        (fun w => re_sub_mul_sepFunctional_coordS a ω₁ ω₂ hD x w)
        (fun t ht => by
          rw [coordS_side₀ a ω₁ ω₂ hD]
          exact ht)
        (fun t ht => by
          rw [coordS_side₁ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
        (fun t ht => by
          rw [coordS_side₂ a ω₁ ω₂ hD]
          have h := Set.mem_Icc.mp ht
          exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
        (fun t ht => by
          rw [coordS_side₃ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
        hx
    · -- `1 < coordS x`: reflect the coordinate
      exact exterior_core a ω₁ ω₂ hD (fun w => 1 - coordS a ω₁ ω₂ w)
        (-sepFunctional ω₂)
        (fun w => by
          show ((w - x) * -sepFunctional ω₂).re
            = latticeCross ω₁ ω₂
              * ((1 - coordS a ω₁ ω₂ w) - (1 - coordS a ω₁ ω₂ x))
          have h := re_sub_mul_sepFunctional_coordS a ω₁ ω₂ hD x w
          rw [mul_neg, Complex.neg_re]
          linear_combination -h)
        (fun t ht => by
          show (1 : ℝ) - coordS a ω₁ ω₂ (side₀ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordS_side₀ a ω₁ ω₂ hD]
          have h := Set.mem_Icc.mp ht
          exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
        (fun t ht => by
          show (1 : ℝ) - coordS a ω₁ ω₂ (side₁ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordS_side₁ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
        (fun t ht => by
          show (1 : ℝ) - coordS a ω₁ ω₂ (side₂ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordS_side₂ a ω₁ ω₂ hD]
          have h := Set.mem_Icc.mp ht
          exact Set.mem_Icc.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)
        (fun t ht => by
          show (1 : ℝ) - coordS a ω₁ ω₂ (side₃ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordS_side₃ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
        (by
          show (1 : ℝ) - coordS a ω₁ ω₂ x < 0
          linarith)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · -- `coordR x < 0`
      exact exterior_core a ω₁ ω₂ hD (coordR a ω₁ ω₂) (-sepFunctional ω₁)
        (fun w => re_sub_mul_neg_sepFunctional_coordR a ω₁ ω₂ hD x w)
        (fun t ht => by
          rw [coordR_side₀ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
        (fun t ht => by
          rw [coordR_side₁ a ω₁ ω₂ hD]
          exact ht)
        (fun t ht => by
          rw [coordR_side₂ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
        (fun t ht => by
          rw [coordR_side₃ a ω₁ ω₂ hD]
          have h := Set.mem_Icc.mp ht
          exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
        hx
    · -- `1 < coordR x`: reflect the coordinate
      exact exterior_core a ω₁ ω₂ hD (fun w => 1 - coordR a ω₁ ω₂ w)
        (sepFunctional ω₁)
        (fun w => by
          show ((w - x) * sepFunctional ω₁).re
            = latticeCross ω₁ ω₂
              * ((1 - coordR a ω₁ ω₂ w) - (1 - coordR a ω₁ ω₂ x))
          have h := re_sub_mul_neg_sepFunctional_coordR a ω₁ ω₂ hD x w
          rw [mul_neg, Complex.neg_re] at h
          linear_combination -h)
        (fun t ht => by
          show (1 : ℝ) - coordR a ω₁ ω₂ (side₀ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordR_side₀ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
        (fun t ht => by
          show (1 : ℝ) - coordR a ω₁ ω₂ (side₁ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordR_side₁ a ω₁ ω₂ hD]
          have h := Set.mem_Icc.mp ht
          exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
        (fun t ht => by
          show (1 : ℝ) - coordR a ω₁ ω₂ (side₂ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordR_side₂ a ω₁ ω₂ hD]
          exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
        (fun t ht => by
          show (1 : ℝ) - coordR a ω₁ ω₂ (side₃ a ω₁ ω₂ t) ∈ Icc (0 : ℝ) 1
          rw [coordR_side₃ a ω₁ ω₂ hD]
          have h := Set.mem_Icc.mp ht
          exact Set.mem_Icc.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)
        (by
          show (1 : ℝ) - coordR a ω₁ ω₂ x < 0
          linarith)

/-! ## Interior winding in coordinates -/

/-- **Interior winding in coordinates**: if both Cramer coordinates of
`x` lie in `(0,1)`, the parallelogram boundary integral of `(z − x)⁻¹`
is `±2πi` with the sign of the orientation. -/
theorem boundaryIntegral_inv_sub_of_coord_interior
    (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hs : coordS a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1)
    (hr : coordR a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1) :
    boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹)
      = (if 0 < latticeCross ω₁ ω₂ then 1 else -1)
        * (2 * Real.pi * Complex.I) := by
  have h := boundaryIntegral_inv_sub_interior a ω₁ ω₂ hD hs hr
  rwa [interiorPt_coords a ω₁ ω₂ hD] at h

end ParallelogramWinding

end JacobianChallenge

end
