/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IteratedMidpointAffineForm

set_option linter.unusedSectionVars false

/-! # Depth-`n` diameter bound on parameter triangles

Strengthening of `isIteratedSubdivision_affine_form` (chip B): the
triple `(A, B, C) ∈ standardSimplex2 × standardSimplex2 × standardSimplex2`
extracted at depth `n` satisfies the **coordinate-wise** pairwise
bound
`|A i - B i| ≤ (1/2)^n, |A i - C i| ≤ (1/2)^n, |B i - C i| ≤ (1/2)^n`
for every `i : Fin 2`.

The base case is `n = 0`, `(A, B, C) = (v0, v1, v2)`, all coord
differences `≤ 1 = (1/2)^0`.

The step case uses the identity
`affineCombo A B C s - affineCombo A B C t
   = (t₀ + t₁ - s₀ - s₁) • A + (s₀ - t₀) • B + (s₁ - t₁) • C`,
which for each of the 4 midpoint-subdivision triples
`(a_i, b_i, c_i)` yields, on each pair, exactly half of one of the
outer pairwise differences `(A - B), (A - C), (B - C)`.

The coordinate-wise bound implies a `dist`-level bound on
`Fin 2 → ℝ` (Pi sup metric) and a `Metric.diam`-level bound on the
parameter sub-triangle `affineCombo A B C '' standardSimplex2`. The
conversion to `Metric.diam` is deferred to the Lebesgue chip (chip D).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

namespace Smooth2Simplex

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Coordinate-wise pairwise bound** on a parameter triple `(A, B, C)`
in `Fin 2 → ℝ`: every pair differs by at most `r` in every coordinate. -/
def ParameterTriangleBound (A B C : Fin 2 → ℝ) (r : ℝ) : Prop :=
  (∀ i, |A i - B i| ≤ r) ∧ (∀ i, |A i - C i| ≤ r) ∧ (∀ i, |B i - C i| ≤ r)

/-- **Base-case bound for `(v0, v1, v2)`.** All three pairwise
coordinate differences are bounded by `1 = (1/2)^0`. -/
private lemma parameterTriangleBound_v0_v1_v2 :
    ParameterTriangleBound Smooth2Simplex.v0 Smooth2Simplex.v1
      Smooth2Simplex.v2 (((1 : ℝ) / 2)^0) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro i
    simp only [Smooth2Simplex.v0, Smooth2Simplex.v1, Smooth2Simplex.v2,
      pow_zero]
    fin_cases i <;> simp

/-- **Halving identity for `affineCombo`.** For any `A, B, C, s, t`,
`affineCombo A B C s i - affineCombo A B C t i
  = (t 0 + t 1 - s 0 - s 1) * A i + (s 0 - t 0) * B i + (s 1 - t 1) * C i`. -/
private lemma affineCombo_sub_coord (A B C s t : Fin 2 → ℝ) (i : Fin 2) :
    Smooth2Simplex.affineCombo A B C s i
        - Smooth2Simplex.affineCombo A B C t i
      = (t 0 + t 1 - s 0 - s 1) * A i
          + (s 0 - t 0) * B i + (s 1 - t 1) * C i := by
  simp only [Smooth2Simplex.affineCombo, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- **Inductive step at level `i = 0` (T0 sub-triangle).**

For `(a, b, c) = (v0, midpoint01, midpoint02)`:
* `affineCombo A B C v0 = A`,
* `affineCombo A B C midpoint01 = (A + B) / 2`,
* `affineCombo A B C midpoint02 = (A + C) / 2`.

Pairwise coord differences halve: `(A - midAB) = (A - B)/2`, etc. -/
private lemma parameterTriangleBound_step_T0
    {A B C : Fin 2 → ℝ} {r : ℝ}
    (h : ParameterTriangleBound A B C r) :
    ParameterTriangleBound
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.v0)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint01)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint02)
      (r / 2) := by
  obtain ⟨hAB, hAC, hBC⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
    rw [affineCombo_sub_coord] <;>
    simp only [Smooth2Simplex.v0, Smooth2Simplex.midpoint01,
      Smooth2Simplex.midpoint02, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  · -- pair 1: v0 vs midpoint01.
    -- t = midpoint01 = (1/2, 0), s = v0 = (0, 0).
    -- t0+t1-s0-s1 = 1/2, s0-t0 = -1/2, s1-t1 = 0.
    -- LHS = (1/2) A i - (1/2) B i = (1/2)(A i - B i).
    -- |LHS| = (1/2)|A i - B i| ≤ r/2.
    have := hAB i
    have hcalc : (1/2 + 0 - 0 - 0) * A i + (0 - 1/2) * B i + (0 - 0) * C i
              = (A i - B i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (A i - B i)]
  · -- pair 2: v0 vs midpoint02.
    -- t = midpoint02 = (0, 1/2), s = v0 = (0, 0).
    -- t0+t1-s0-s1 = 1/2, s0-t0 = 0, s1-t1 = -1/2.
    have := hAC i
    have hcalc : (0 + 1/2 - 0 - 0) * A i + (0 - 0) * B i + (0 - 1/2) * C i
              = (A i - C i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (A i - C i)]
  · -- pair 3: midpoint01 vs midpoint02.
    -- t = midpoint02 = (0, 1/2), s = midpoint01 = (1/2, 0).
    -- t0+t1-s0-s1 = 0+1/2-1/2-0 = 0, s0-t0 = 1/2, s1-t1 = -1/2.
    have := hBC i
    have hcalc : (0 + 1/2 - 1/2 - 0) * A i + (1/2 - 0) * B i + (0 - 1/2) * C i
              = (B i - C i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (B i - C i)]

/-- **Inductive step at level `i = 1` (T1 sub-triangle).**

For `(a, b, c) = (midpoint01, v1, midpoint12)`:
* `affineCombo A B C midpoint01 = (A + B) / 2`,
* `affineCombo A B C v1 = B`,
* `affineCombo A B C midpoint12 = (B + C) / 2`. -/
private lemma parameterTriangleBound_step_T1
    {A B C : Fin 2 → ℝ} {r : ℝ}
    (h : ParameterTriangleBound A B C r) :
    ParameterTriangleBound
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint01)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.v1)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint12)
      (r / 2) := by
  obtain ⟨hAB, hAC, hBC⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
    rw [affineCombo_sub_coord] <;>
    simp only [Smooth2Simplex.v1, Smooth2Simplex.midpoint01,
      Smooth2Simplex.midpoint12, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  · -- pair midpoint01 vs v1: (1/2 - 1) A + (1) B = (A + B)/2 - B = -(A - B)/2... wait
    -- s = midpoint01 = (1/2, 0), t = v1 = (1, 0).
    -- t0+t1-s0-s1 = 1+0-1/2-0 = 1/2, s0-t0 = 1/2-1 = -1/2, s1-t1 = 0.
    -- LHS = (1/2) A + (-1/2) B = (A - B)/2.
    have := hAB i
    have hcalc : (1 + 0 - 1/2 - 0) * A i + (1/2 - 1) * B i + (0 - 0) * C i
              = (A i - B i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (A i - B i)]
  · -- pair midpoint01 vs midpoint12.
    -- s = midpoint01 = (1/2, 0), t = midpoint12 = (1/2, 1/2).
    -- t0+t1-s0-s1 = 1/2+1/2-1/2-0 = 1/2, s0-t0 = 0, s1-t1 = -1/2.
    -- LHS = (1/2) A + 0 + (-1/2) C = (A - C)/2.
    have := hAC i
    have hcalc : (1/2 + 1/2 - 1/2 - 0) * A i + (1/2 - 1/2) * B i
                  + (0 - 1/2) * C i
              = (A i - C i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (A i - C i)]
  · -- pair v1 vs midpoint12.
    -- s = v1 = (1, 0), t = midpoint12 = (1/2, 1/2).
    -- t0+t1-s0-s1 = 1/2+1/2-1-0 = 0, s0-t0 = 1-1/2 = 1/2, s1-t1 = -1/2.
    -- LHS = 0 + (1/2) B + (-1/2) C = (B - C)/2.
    have := hBC i
    have hcalc : (1/2 + 1/2 - 1 - 0) * A i + (1 - 1/2) * B i
                  + (0 - 1/2) * C i
              = (B i - C i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (B i - C i)]

/-- **Inductive step at level `i = 2` (T2 sub-triangle).**

For `(a, b, c) = (midpoint02, midpoint12, v2)`. -/
private lemma parameterTriangleBound_step_T2
    {A B C : Fin 2 → ℝ} {r : ℝ}
    (h : ParameterTriangleBound A B C r) :
    ParameterTriangleBound
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint02)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint12)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.v2)
      (r / 2) := by
  obtain ⟨hAB, hAC, hBC⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
    rw [affineCombo_sub_coord] <;>
    simp only [Smooth2Simplex.v2, Smooth2Simplex.midpoint02,
      Smooth2Simplex.midpoint12, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  · -- pair midpoint02 vs midpoint12.
    -- s = (0, 1/2), t = (1/2, 1/2).
    have := hAB i
    have hcalc : (1/2 + 1/2 - 0 - 1/2) * A i + (0 - 1/2) * B i
                  + (1/2 - 1/2) * C i
              = (A i - B i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (A i - B i)]
  · -- pair midpoint02 vs v2.
    -- s = (0, 1/2), t = v2 = (0, 1).
    have := hAC i
    have hcalc : (0 + 1 - 0 - 1/2) * A i + (0 - 0) * B i + (1/2 - 1) * C i
              = (A i - C i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (A i - C i)]
  · -- pair midpoint12 vs v2.
    -- s = (1/2, 1/2), t = (0, 1).
    have := hBC i
    have hcalc : (0 + 1 - 1/2 - 1/2) * A i + (1/2 - 0) * B i
                  + (1/2 - 1) * C i
              = (B i - C i) / 2 := by ring
    rw [hcalc]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg (B i - C i)]

/-- **Inductive step at level `i = 3` (T3 sub-triangle).**

For `(a, b, c) = (midpoint12, midpoint02, midpoint01)`. -/
private lemma parameterTriangleBound_step_T3
    {A B C : Fin 2 → ℝ} {r : ℝ}
    (h : ParameterTriangleBound A B C r) :
    ParameterTriangleBound
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint12)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint02)
      (Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint01)
      (r / 2) := by
  obtain ⟨hAB, hAC, hBC⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;>
    rw [affineCombo_sub_coord] <;>
    simp only [Smooth2Simplex.midpoint01, Smooth2Simplex.midpoint02,
      Smooth2Simplex.midpoint12, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  · -- pair midpoint12 vs midpoint02.
    -- s = (1/2, 1/2), t = (0, 1/2).
    have hH := hAB i
    have hcalc : (0 + 1/2 - 1/2 - 1/2) * A i + (1/2 - 0) * B i
                  + (1/2 - 1/2) * C i
              = (B i - A i) / 2 := by ring
    rw [hcalc, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_sub_comm]
    linarith [abs_nonneg (A i - B i)]
  · -- pair midpoint12 vs midpoint01.
    -- s = (1/2, 1/2), t = (1/2, 0).
    have hH := hAC i
    have hcalc : (1/2 + 0 - 1/2 - 1/2) * A i + (1/2 - 1/2) * B i
                  + (1/2 - 0) * C i
              = (C i - A i) / 2 := by ring
    rw [hcalc, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_sub_comm]
    linarith [abs_nonneg (A i - C i)]
  · -- pair midpoint02 vs midpoint01.
    -- s = (0, 1/2), t = (1/2, 0).
    have hH := hBC i
    have hcalc : (1/2 + 0 - 0 - 1/2) * A i + (0 - 1/2) * B i
                  + (1/2 - 0) * C i
              = (C i - B i) / 2 := by ring
    rw [hcalc, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_sub_comm]
    linarith [abs_nonneg (B i - C i)]

/-! ## Strengthened affine form theorem with diameter bound -/

/-- **Strengthened affine form with depth-`n` diameter bound.**

For `IsIteratedSubdivision σ n T`, there exist `A B C ∈ standardSimplex2`
with `T.toFun = (affineReparam σ A B C).toFun`, *and* with the
coordinate-wise pairwise bound
`ParameterTriangleBound A B C ((1/2)^n)`.

Proof by induction on the predicate; the step case selects the right
sub-triangle bound (`T0/T1/T2/T3`) by `fin_cases` and applies the
corresponding halving lemma above. -/
theorem isIteratedSubdivision_affine_form_with_diam_bound
    {σ T : Smooth2Simplex 𝓘(ℝ, ℂ) X} {n : ℕ}
    (h : IsIteratedSubdivision σ n T) :
    ∃ A B C : Fin 2 → ℝ,
      A ∈ standardSimplex2 ∧ B ∈ standardSimplex2 ∧ C ∈ standardSimplex2 ∧
      ParameterTriangleBound A B C (((1 : ℝ) / 2)^n) ∧
      T.toFun = (Smooth2Simplex.affineReparam σ A B C).toFun := by
  induction h with
  | refl =>
      refine ⟨Smooth2Simplex.v0, Smooth2Simplex.v1, Smooth2Simplex.v2,
        Smooth2Simplex.v0_mem_standardSimplex2,
        Smooth2Simplex.v1_mem_standardSimplex2,
        Smooth2Simplex.v2_mem_standardSimplex2,
        parameterTriangleBound_v0_v1_v2,
        toFun_eq_affineReparam_v0_v1_v2 σ⟩
  | @step T_prev n h_prev i ih =>
      obtain ⟨A, B, C, hA, hB, hC, h_bound, h_eq⟩ := ih
      -- The new triple is (affineCombo A B C a_i, affineCombo A B C b_i,
      -- affineCombo A B C c_i) where (a_i, b_i, c_i) is determined by i.
      -- Membership: each lies in standardSimplex2 by
      -- affineCombo_mem_standardSimplex2.
      -- Bound: r/2 = (1/2)^n / 2 = (1/2)^(n+1) — apply the appropriate
      -- T0/T1/T2/T3 halving.
      -- toFun equality: chip A composition + h_eq, as in chip B.
      have h_pow : ((1 : ℝ) / 2)^n / 2 = ((1 : ℝ) / 2)^(n+1) := by
        rw [pow_succ]; ring
      -- For all four i, the new triple uses two of {v0, v1, v2,
      -- midpoint01, midpoint12, midpoint02}, all in Δ².
      fin_cases i
      · refine ⟨Smooth2Simplex.affineCombo A B C Smooth2Simplex.v0,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint01,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint02,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.v0_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint01_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint02_mem_standardSimplex2, ?_, ?_⟩
        · rw [← h_pow]
          exact parameterTriangleBound_step_T0 h_bound
        · -- defeq: midpointSubdivision T_prev ⟨0, _⟩
          --   = affineReparam T_prev v0 midpoint01 midpoint02
          funext t
          exact (congrFun h_eq (Smooth2Simplex.affineCombo
              Smooth2Simplex.v0 Smooth2Simplex.midpoint01
              Smooth2Simplex.midpoint02 t)).trans
            (congrArg σ.toFun
              (congrFun (Smooth2Simplex.affineCombo_comp A B C
                Smooth2Simplex.v0 Smooth2Simplex.midpoint01
                Smooth2Simplex.midpoint02) t))
      · refine ⟨Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint01,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.v1,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint12,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint01_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.v1_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint12_mem_standardSimplex2, ?_, ?_⟩
        · rw [← h_pow]
          exact parameterTriangleBound_step_T1 h_bound
        · funext t
          exact (congrFun h_eq (Smooth2Simplex.affineCombo
              Smooth2Simplex.midpoint01 Smooth2Simplex.v1
              Smooth2Simplex.midpoint12 t)).trans
            (congrArg σ.toFun
              (congrFun (Smooth2Simplex.affineCombo_comp A B C
                Smooth2Simplex.midpoint01 Smooth2Simplex.v1
                Smooth2Simplex.midpoint12) t))
      · refine ⟨Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint02,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint12,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.v2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint02_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint12_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.v2_mem_standardSimplex2, ?_, ?_⟩
        · rw [← h_pow]
          exact parameterTriangleBound_step_T2 h_bound
        · funext t
          exact (congrFun h_eq (Smooth2Simplex.affineCombo
              Smooth2Simplex.midpoint02 Smooth2Simplex.midpoint12
              Smooth2Simplex.v2 t)).trans
            (congrArg σ.toFun
              (congrFun (Smooth2Simplex.affineCombo_comp A B C
                Smooth2Simplex.midpoint02 Smooth2Simplex.midpoint12
                Smooth2Simplex.v2) t))
      · refine ⟨Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint12,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint02,
          Smooth2Simplex.affineCombo A B C Smooth2Simplex.midpoint01,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint12_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint02_mem_standardSimplex2,
          Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC
            Smooth2Simplex.midpoint01_mem_standardSimplex2, ?_, ?_⟩
        · rw [← h_pow]
          exact parameterTriangleBound_step_T3 h_bound
        · funext t
          exact (congrFun h_eq (Smooth2Simplex.affineCombo
              Smooth2Simplex.midpoint12 Smooth2Simplex.midpoint02
              Smooth2Simplex.midpoint01 t)).trans
            (congrArg σ.toFun
              (congrFun (Smooth2Simplex.affineCombo_comp A B C
                Smooth2Simplex.midpoint12 Smooth2Simplex.midpoint02
                Smooth2Simplex.midpoint01) t))

/-- **Diameter bound for members of `iteratedMidpointList`.** Combines
`isIteratedSubdivision_of_mem_iteratedMidpointList` with
`isIteratedSubdivision_affine_form_with_diam_bound`. -/
theorem iteratedMidpointList_affine_form_with_diam_bound
    {σ : Smooth2Simplex 𝓘(ℝ, ℂ) X} {n : ℕ}
    {T : Smooth2Simplex 𝓘(ℝ, ℂ) X}
    (hT : T ∈ Smooth2Simplex.iteratedMidpointList σ n) :
    ∃ A B C : Fin 2 → ℝ,
      A ∈ standardSimplex2 ∧ B ∈ standardSimplex2 ∧ C ∈ standardSimplex2 ∧
      ParameterTriangleBound A B C (((1 : ℝ) / 2)^n) ∧
      T.toFun = (Smooth2Simplex.affineReparam σ A B C).toFun :=
  isIteratedSubdivision_affine_form_with_diam_bound
    (isIteratedSubdivision_of_mem_iteratedMidpointList σ n T hT)

end Smooth2Simplex

end JacobianChallenge

end
