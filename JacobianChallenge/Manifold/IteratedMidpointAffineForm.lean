/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IteratedMidpointSubdivision
import JacobianChallenge.Manifold.Smooth2SimplexAffineReparamComp
import JacobianChallenge.Manifold.MidpointSubdivisionChartContained

set_option linter.unusedSectionVars false

/-! # Affine-reparametrization form for elements of `iteratedMidpointList`

Every `T ∈ iteratedMidpointList σ n` has the form
`T.toFun = (affineReparam σ A B C).toFun` for some
`A B C ∈ standardSimplex2`.

We prove this by introducing an inductive predicate
`IsIteratedSubdivision σ n T` (which mirrors the recursive structure
of `iteratedMidpointList`) and then induct on it, using the
composition identity `affineReparam_comp_toFun` to flatten each
recursive step into a single `affineReparam`.

This is the structural prerequisite for the depth-`n` diameter bound
(chip C): once each `T` is expressed as a single `affineReparam σ A B C`,
the parameter-side image `affineCombo A B C '' standardSimplex2` is
an explicit convex hull of `{A, B, C}` whose diameter can be bounded.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

namespace Smooth2Simplex

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Inductive predicate: `T` arises from `σ` by `n` midpoint subdivisions -/

/-- **`IsIteratedSubdivision σ n T`**: `T` arises from `σ` by exactly
`n` applications of `midpointSubdivision`. The base case is `T = σ`
at depth `0`; the step case picks one of the four sub-simplices of
the previous level. -/
inductive IsIteratedSubdivision (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) :
    ℕ → Smooth2Simplex 𝓘(ℝ, ℂ) X → Prop
  | refl : IsIteratedSubdivision σ 0 σ
  | step {T : Smooth2Simplex 𝓘(ℝ, ℂ) X} {n : ℕ}
      (h : IsIteratedSubdivision σ n T) (i : Fin 4) :
      IsIteratedSubdivision σ (n + 1) (Smooth2Simplex.midpointSubdivision T i)

/-- Membership in the iterated-midpoint list implies the predicate. -/
theorem isIteratedSubdivision_of_mem_iteratedMidpointList
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) :
    ∀ (n : ℕ) (T : Smooth2Simplex 𝓘(ℝ, ℂ) X),
      T ∈ Smooth2Simplex.iteratedMidpointList σ n →
      IsIteratedSubdivision σ n T
  | 0, T, hT => by
      rw [Smooth2Simplex.iteratedMidpointList_zero,
          List.mem_singleton] at hT
      subst hT
      exact IsIteratedSubdivision.refl
  | n + 1, T, hT => by
      rw [Smooth2Simplex.iteratedMidpointList_succ,
          List.mem_flatMap] at hT
      obtain ⟨T', hT'_mem, hT_mem⟩ := hT
      rw [List.mem_ofFn] at hT_mem
      obtain ⟨i, hi⟩ := hT_mem
      have h_ih :=
        isIteratedSubdivision_of_mem_iteratedMidpointList σ n T' hT'_mem
      rw [← hi]
      exact IsIteratedSubdivision.step h_ih i

/-! ## Affine form for an iterated midpoint subdivision

Each `T = midpointSubdivision T' i` is an `affineReparam T' a b c`
for one of six fixed `(a, b, c)`-triples drawn from
`{v0, v1, v2, midpoint01, midpoint12, midpoint02}`, all of which lie
in `standardSimplex2`. Combined with `affineReparam_comp_toFun` and
the fact that affine combinations of Δ²-vectors with Δ²-weights stay
in Δ² (`affineCombo_mem_standardSimplex2`), we get a single-affine
form `T.toFun = (affineReparam σ A B C).toFun` with `A B C ∈ Δ²`. -/

/-- **`affineCombo Smooth2Simplex.v0 v1 v2 = id`** on `Fin 2 → ℝ`. The
identity affine combination: weights `(1 - t₀ - t₁, t₀, t₁)` against
`(0,0), (1,0), (0,1)` reproduce `(t₀, t₁) = t`. -/
@[simp] lemma affineCombo_v0_v1_v2_eq_id :
    Smooth2Simplex.affineCombo Smooth2Simplex.v0 Smooth2Simplex.v1
        Smooth2Simplex.v2
      = id := by
  funext t i
  simp only [Smooth2Simplex.affineCombo, Smooth2Simplex.v0,
    Smooth2Simplex.v1, Smooth2Simplex.v2,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq]
  fin_cases i <;> simp

/-- **`σ.toFun = (affineReparam σ v0 v1 v2).toFun`** — every smooth
2-simplex is its own affine reparameterisation with vertices the
standard `Δ²` corners. -/
lemma toFun_eq_affineReparam_v0_v1_v2 (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) :
    σ.toFun
      = (Smooth2Simplex.affineReparam σ Smooth2Simplex.v0
          Smooth2Simplex.v1 Smooth2Simplex.v2).toFun := by
  funext t
  simp only [Smooth2Simplex.affineReparam_apply,
    affineCombo_v0_v1_v2_eq_id, id_eq]

/-- **Triples of `(a, b, c)` used by `midpointSubdivision`.** All lie
in `standardSimplex2 × standardSimplex2 × standardSimplex2`. -/
private lemma midpointSubdivision_vertex_triple_mem_standardSimplex2 (i : Fin 4) :
    ∃ a b c : Fin 2 → ℝ,
      a ∈ standardSimplex2 ∧ b ∈ standardSimplex2 ∧ c ∈ standardSimplex2 ∧
      (∀ T : Smooth2Simplex 𝓘(ℝ, ℂ) X,
        Smooth2Simplex.midpointSubdivision T i
          = Smooth2Simplex.affineReparam T a b c) := by
  fin_cases i
  · exact ⟨Smooth2Simplex.v0, Smooth2Simplex.midpoint01,
      Smooth2Simplex.midpoint02,
      Smooth2Simplex.v0_mem_standardSimplex2,
      Smooth2Simplex.midpoint01_mem_standardSimplex2,
      Smooth2Simplex.midpoint02_mem_standardSimplex2,
      fun T => Smooth2Simplex.midpointSubdivision_T0 T⟩
  · exact ⟨Smooth2Simplex.midpoint01, Smooth2Simplex.v1,
      Smooth2Simplex.midpoint12,
      Smooth2Simplex.midpoint01_mem_standardSimplex2,
      Smooth2Simplex.v1_mem_standardSimplex2,
      Smooth2Simplex.midpoint12_mem_standardSimplex2,
      fun T => Smooth2Simplex.midpointSubdivision_T1 T⟩
  · exact ⟨Smooth2Simplex.midpoint02, Smooth2Simplex.midpoint12,
      Smooth2Simplex.v2,
      Smooth2Simplex.midpoint02_mem_standardSimplex2,
      Smooth2Simplex.midpoint12_mem_standardSimplex2,
      Smooth2Simplex.v2_mem_standardSimplex2,
      fun T => Smooth2Simplex.midpointSubdivision_T2 T⟩
  · exact ⟨Smooth2Simplex.midpoint12, Smooth2Simplex.midpoint02,
      Smooth2Simplex.midpoint01,
      Smooth2Simplex.midpoint12_mem_standardSimplex2,
      Smooth2Simplex.midpoint02_mem_standardSimplex2,
      Smooth2Simplex.midpoint01_mem_standardSimplex2,
      fun T => Smooth2Simplex.midpointSubdivision_T3 T⟩

/-- **Affine form for iterated midpoint subdivisions.** Given
`IsIteratedSubdivision σ n T`, there exist `A, B, C ∈ standardSimplex2`
such that `T.toFun = (affineReparam σ A B C).toFun`. -/
theorem isIteratedSubdivision_affine_form
    {σ T : Smooth2Simplex 𝓘(ℝ, ℂ) X} {n : ℕ}
    (h : IsIteratedSubdivision σ n T) :
    ∃ A B C : Fin 2 → ℝ,
      A ∈ standardSimplex2 ∧ B ∈ standardSimplex2 ∧ C ∈ standardSimplex2 ∧
      T.toFun = (Smooth2Simplex.affineReparam σ A B C).toFun := by
  induction h with
  | refl =>
      exact ⟨Smooth2Simplex.v0, Smooth2Simplex.v1, Smooth2Simplex.v2,
        Smooth2Simplex.v0_mem_standardSimplex2,
        Smooth2Simplex.v1_mem_standardSimplex2,
        Smooth2Simplex.v2_mem_standardSimplex2,
        toFun_eq_affineReparam_v0_v1_v2 σ⟩
  | step h_prev i ih =>
      obtain ⟨A, B, C, hA, hB, hC, h_eq⟩ := ih
      obtain ⟨a, b, c, ha, hb, hc, h_sub⟩ :=
        midpointSubdivision_vertex_triple_mem_standardSimplex2 (X := X) i
      refine ⟨Smooth2Simplex.affineCombo A B C a,
        Smooth2Simplex.affineCombo A B C b,
        Smooth2Simplex.affineCombo A B C c,
        Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC ha,
        Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC hb,
        Smooth2Simplex.affineCombo_mem_standardSimplex2 hA hB hC hc, ?_⟩
      -- (midpointSubdivision T_step i) = (affineReparam T_step a b c) via h_sub;
      -- (T_step.toFun) = (affineReparam σ A B C).toFun via h_eq;
      -- compose with affineCombo_comp (chip A). T_step is the implicit binder
      -- from the inductive step — to avoid naming it, we chain via .trans on
      -- congrFun h_eq and congrArg σ.toFun ∘ congrFun affineCombo_comp.
      -- All `affineReparam ?.toFun` reductions are `rfl` (defeq).
      rw [h_sub]
      funext t
      exact (congrFun h_eq (Smooth2Simplex.affineCombo a b c t)).trans
        (congrArg σ.toFun
          (congrFun (Smooth2Simplex.affineCombo_comp A B C a b c) t))

/-- **Affine form for members of `iteratedMidpointList`.** Compose
`isIteratedSubdivision_of_mem_iteratedMidpointList` with
`isIteratedSubdivision_affine_form`. -/
theorem iteratedMidpointList_affine_form
    {σ : Smooth2Simplex 𝓘(ℝ, ℂ) X} {n : ℕ}
    {T : Smooth2Simplex 𝓘(ℝ, ℂ) X}
    (hT : T ∈ Smooth2Simplex.iteratedMidpointList σ n) :
    ∃ A B C : Fin 2 → ℝ,
      A ∈ standardSimplex2 ∧ B ∈ standardSimplex2 ∧ C ∈ standardSimplex2 ∧
      T.toFun = (Smooth2Simplex.affineReparam σ A B C).toFun :=
  isIteratedSubdivision_affine_form
    (isIteratedSubdivision_of_mem_iteratedMidpointList σ n T hT)

end Smooth2Simplex

end JacobianChallenge

end
