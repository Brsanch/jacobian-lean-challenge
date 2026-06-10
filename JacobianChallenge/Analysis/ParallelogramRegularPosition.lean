/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramCoordinates
import Mathlib.Analysis.Real.Cardinality

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Regular position: a base point avoiding all lattice translates

Piece 4 of the forward-Abel contour argument (`HANDOFF_TLDIVSUM.md`):
for every finite set `P` of base points there is a base point `a` such
that **every** lattice translate `p + m₁·ω₁ + m₂·ω₂` (`p ∈ P`,
`m₁ m₂ : ℤ`) has both Cramer coordinates relative to `Π(a; ω₁, ω₂)`
avoiding `{0, 1}` (`exists_regular_position`).

In coordinates the argument is one line: for `a = σ·ω₁ + ρ·ω₂` the
translate's `s`-coordinate is `s_p + m₁ − σ`, so the bad `σ`-set is the
countable union `⋃_p (s_p + ℤ)` — and `ℝ` is uncountable
(`Cardinal.not_countable_real`).

Consequences packaged here for the assembly:

* `sideX_ne_of_coord...` — a point with coordinates off `{0,1}` is not
  on any of the four sides (so the contour avoids all poles);
* `boundaryIntegral_inv_sub_of_coord_ne` — the **single evaluator**:
  for such a point the winding integral equals `±2πi` if both
  coordinates lie in `(0,1)` (interior) and `0` otherwise (exterior),
  by the `ParallelogramCoordinates.lean` dichotomy.

No `sorry`, no `axiom`. -/

noncomputable section

open Set

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-! ## Countable avoidance -/

/-- A real number avoiding the integer translates of finitely many
values: the bad set is countable, `ℝ` is not. -/
lemma exists_real_avoiding_int_translates (P : Finset ℂ) (g : ℂ → ℝ) :
    ∃ σ : ℝ, ∀ p ∈ P, ∀ m : ℤ, σ ≠ g p + m := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set ℝ)
      ⊆ ⋃ p ∈ (P : Set ℂ), Set.range (fun m : ℤ => g p + m) := by
    intro σ _
    obtain ⟨p, hp, m, hm⟩ := h σ
    exact Set.mem_biUnion (Finset.mem_coe.mpr hp) ⟨m, hm.symm⟩
  have hcount : (⋃ p ∈ (P : Set ℂ),
      Set.range (fun m : ℤ => g p + m)).Countable :=
    P.countable_toSet.biUnion (fun p _ => Set.countable_range _)
  exact Cardinal.not_countable_real (hcount.mono hsub)

/-! ## Coordinates of lattice translates -/

/-- The `s`-coordinate of a lattice translate relative to the base
point `σ·ω₁ + ρ·ω₂`. -/
lemma coordS_translate (hD : latticeCross ω₁ ω₂ ≠ 0) (σ ρ : ℝ)
    (p : ℂ) (m₁ m₂ : ℤ) :
    coordS (σ • ω₁ + ρ • ω₂) ω₁ ω₂ (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂)
      = latticeCross p ω₂ / latticeCross ω₁ ω₂ + m₁ - σ := by
  rw [coordS]
  have hcross : latticeCross
      (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂ - (σ • ω₁ + ρ • ω₂)) ω₂
      = latticeCross p ω₂ + ((m₁ : ℝ) - σ) * latticeCross ω₁ ω₂ := by
    simp only [latticeCross, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.real_smul,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hcross, add_div, mul_div_assoc, div_self hD, mul_one]
  ring

/-- The `r`-coordinate of a lattice translate relative to the base
point `σ·ω₁ + ρ·ω₂`. -/
lemma coordR_translate (hD : latticeCross ω₁ ω₂ ≠ 0) (σ ρ : ℝ)
    (p : ℂ) (m₁ m₂ : ℤ) :
    coordR (σ • ω₁ + ρ • ω₂) ω₁ ω₂ (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂)
      = latticeCross ω₁ p / latticeCross ω₁ ω₂ + m₂ - ρ := by
  rw [coordR]
  have hcross : latticeCross ω₁
      (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂ - (σ • ω₁ + ρ • ω₂))
      = latticeCross ω₁ p + ((m₂ : ℝ) - ρ) * latticeCross ω₁ ω₂ := by
    simp only [latticeCross, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.real_smul,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hcross, add_div, mul_div_assoc, div_self hD, mul_one]
  ring

/-! ## Regular position -/

/-- **Regular position** (piece 4): there is a base point `a` such that
every lattice translate `p + m₁·ω₁ + m₂·ω₂` of every `p ∈ P` has both
Cramer coordinates relative to `Π(a; ω₁, ω₂)` off `{0, 1}` — so the
boundary `∂Π(a)` avoids all translates and each translate falls in the
interior/exterior winding dichotomy. -/
theorem exists_regular_position (hD : latticeCross ω₁ ω₂ ≠ 0)
    (P : Finset ℂ) :
    ∃ a : ℂ, ∀ p ∈ P, ∀ m₁ m₂ : ℤ,
      coordS a ω₁ ω₂ (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 0 ∧
      coordS a ω₁ ω₂ (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 1 ∧
      coordR a ω₁ ω₂ (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 0 ∧
      coordR a ω₁ ω₂ (p + (m₁ : ℂ) * ω₁ + (m₂ : ℂ) * ω₂) ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_real_avoiding_int_translates P
    (fun p => latticeCross p ω₂ / latticeCross ω₁ ω₂)
  obtain ⟨ρ, hρ⟩ := exists_real_avoiding_int_translates P
    (fun p => latticeCross ω₁ p / latticeCross ω₁ ω₂)
  refine ⟨σ • ω₁ + ρ • ω₂, fun p hp m₁ m₂ => ?_⟩
  rw [coordS_translate ω₁ ω₂ hD σ ρ p m₁ m₂,
    coordR_translate ω₁ ω₂ hD σ ρ p m₁ m₂]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hσ p hp m₁ (by linarith)
  · intro h
    apply hσ p hp (m₁ - 1)
    push_cast
    linarith
  · intro h
    exact hρ p hp m₂ (by linarith)
  · intro h
    apply hρ p hp (m₂ - 1)
    push_cast
    linarith

/-! ## A point with coordinates off `{0,1}` is not on the boundary -/

lemma side₀_ne_of_coordR_ne_zero (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hr0 : coordR a ω₁ ω₂ x ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t ≠ x := by
  intro t ht h
  apply hr0
  rw [← h, coordR_side₀ a ω₁ ω₂ hD]

lemma side₁_ne_of_coordS_ne_one (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hs1 : coordS a ω₁ ω₂ x ≠ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t ≠ x := by
  intro t ht h
  apply hs1
  rw [← h, coordS_side₁ a ω₁ ω₂ hD]

lemma side₂_ne_of_coordR_ne_one (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hr1 : coordR a ω₁ ω₂ x ≠ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t ≠ x := by
  intro t ht h
  apply hr1
  rw [← h, coordR_side₂ a ω₁ ω₂ hD]

lemma side₃_ne_of_coordS_ne_zero (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hs0 : coordS a ω₁ ω₂ x ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t ≠ x := by
  intro t ht h
  apply hs0
  rw [← h, coordS_side₃ a ω₁ ω₂ hD]

/-! ## The single winding evaluator -/

/-- **The winding evaluator at a regular-position point**: if both
coordinates of `x` avoid `{0,1}`, the winding integral is `±2πi` when
`x` is interior (both coordinates in `(0,1)`) and `0` otherwise. -/
theorem boundaryIntegral_inv_sub_of_coord_ne
    (hD : latticeCross ω₁ ω₂ ≠ 0) {x : ℂ}
    (hs0 : coordS a ω₁ ω₂ x ≠ 0) (hs1 : coordS a ω₁ ω₂ x ≠ 1)
    (hr0 : coordR a ω₁ ω₂ x ≠ 0) (hr1 : coordR a ω₁ ω₂ x ≠ 1) :
    boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹)
      = if coordS a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1
            ∧ coordR a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1
        then (if 0 < latticeCross ω₁ ω₂ then 1 else -1)
          * (2 * Real.pi * Complex.I)
        else 0 := by
  by_cases hin : coordS a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1
      ∧ coordR a ω₁ ω₂ x ∈ Ioo (0 : ℝ) 1
  · rw [if_pos hin]
    exact boundaryIntegral_inv_sub_of_coord_interior a ω₁ ω₂ hD
      hin.1 hin.2
  · rw [if_neg hin]
    apply boundaryIntegral_inv_sub_of_coord_exterior a ω₁ ω₂ hD
    rcases not_and_or.mp hin with h | h
    · left
      intro hmem
      apply h
      obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hmem
      exact Set.mem_Ioo.mpr
        ⟨lt_of_le_of_ne h0 (Ne.symm hs0), lt_of_le_of_ne h1 hs1⟩
    · right
      intro hmem
      apply h
      obtain ⟨h0, h1⟩ := Set.mem_Icc.mp hmem
      exact Set.mem_Ioo.mpr
        ⟨lt_of_le_of_ne h0 (Ne.symm hr0), lt_of_le_of_ne h1 hr1⟩

end ParallelogramWinding

end JacobianChallenge

end
