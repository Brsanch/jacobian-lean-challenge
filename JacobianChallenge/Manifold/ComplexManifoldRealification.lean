/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Realification of a holomorphic 1-manifold structure

A complex 1-manifold modelled on `(ℂ, ℂ)` over the holomorphic model with
corners `𝓘(ℂ, ℂ)` is automatically a real `C^n` manifold modelled on the same
`(ℂ, ℂ)` underlying chart shape but over the *real* model with corners
`𝓘(ℝ, ℂ)`, for every regularity exponent `n : WithTop ℕ∞`.

This is the structural prerequisite for the period-pairing arc (chip PL-1):
to interpret a holomorphic 1-form as a pair of smooth real 1-forms via the
pointwise real/imaginary split already supplied by
`Manifold/HolomorphicOneFormRealification.lean`, we need the ambient
`SmoothOneForm 𝓘(ℝ, ℂ) X` to be well-formed, which requires
`[IsManifold 𝓘(ℝ, ℂ) ⊤ X]` as an instance.

The bridge in this file supplies precisely that instance, deriving it from
the holomorphic structure `[IsManifold 𝓘(ℂ, ℂ) ω X]` already in the repo.

## Main results

* `JacobianChallenge.contDiffOn_real_chart_trans_of_complex` — the
  load-bearing function-level fact: each holomorphic chart transition is a
  `ContDiffOn ℝ n` map on its source.
* `JacobianChallenge.complexManifoldRealification` — an `instance` upgrading
  `[IsManifold 𝓘(ℂ, ℂ) ω X]` to `IsManifold 𝓘(ℝ, ℂ) n X` for any `n`.

## Strategy

`isManifold_of_contDiffOn` (mathlib `IsManifold/Basic.lean`) reduces the
construction of an `IsManifold I n M` instance to the chart-transition
`ContDiffOn` statement. For our `I = 𝓘(ℝ, ℂ)` target:

* The existing holomorphic structure `[IsManifold 𝓘(ℂ, ℂ) ω X]` supplies
  the same chart transition as a member of `contDiffGroupoid ω 𝓘(ℂ, ℂ)`,
  which unfolds (via `mem_groupoid_of_pregroupoid` + `contDiffPregroupoid`)
  to a `ContDiffOn ℂ ω` statement.
* Both `𝓘(ℝ, ℂ)` and `𝓘(ℂ, ℂ)` are coercion-equal to the identity on `ℂ`
  (`modelWithCornersSelf_coe`, `modelWithCornersSelf_coe_symm`) and have
  `range = univ` (boundarylessness), so the surrounding `I ∘ … ∘ I.symm`
  and `I.symm ⁻¹' … ∩ range I` expressions are simp-equal between the two
  models.
* `ContDiffOn.of_le` (mathlib `ContDiff/Operations.lean`) downgrades
  regularity `ω ≤ ⊤` to any `n ≤ ω`.
* `ContDiffOn.restrict_scalars` (same file, line ~1054) downgrades the
  scalar field `ℂ` to `ℝ` using the standing `[NormedAlgebra ℝ ℂ]`,
  `[IsScalarTower ℝ ℂ ℂ]` instances.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Set Function

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Chart transitions of a holomorphic 1-manifold are real-smooth.**

If `X` carries a holomorphic `[IsManifold 𝓘(ℂ, ℂ) ω X]` structure, then for
every pair of charts `(e, e')` in the atlas and every regularity exponent
`n : WithTop ℕ∞`, the conjugated chart transition
`𝓘(ℝ, ℂ) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℝ, ℂ).symm` is `ContDiffOn ℝ n` on its
canonical source `𝓘(ℝ, ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range 𝓘(ℝ, ℂ)`.

This is the input to `isManifold_of_contDiffOn` for building the real
`IsManifold 𝓘(ℝ, ℂ) n X` instance. -/
theorem contDiffOn_real_chart_trans_of_complex
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    (e e' : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (he' : e' ∈ atlas ℂ X)
    (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (𝓘(ℝ, ℂ) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℝ, ℂ).symm)
      (𝓘(ℝ, ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range 𝓘(ℝ, ℂ)) := by
  -- Reduce both the holomorphic and target statements to the un-conjugated
  -- chart-transition form on its source. `𝓘(ℝ, ℂ)` and `𝓘(ℂ, ℂ)` are both
  -- coercion-equal to `id` on `ℂ`, with `range = univ`, so the
  -- conjugated form equals the underlying chart transition on its source.
  suffices h_real : ContDiffOn ℝ n (↑(e.symm ≫ₕ e')) (e.symm ≫ₕ e').source by
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ]
    exact h_real
  -- Extract the holomorphic chart compatibility from the existing manifold structure
  -- and reduce it to the same un-conjugated form.
  have h_fwd : ContDiffOn ℂ ω (↑(e.symm ≫ₕ e')) (e.symm ≫ₕ e').source := by
    have h_compat : (e.symm ≫ₕ e') ∈ contDiffGroupoid ω 𝓘(ℂ, ℂ) :=
      StructureGroupoid.compatible (contDiffGroupoid ω 𝓘(ℂ, ℂ)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h_compat
    obtain ⟨h, _⟩ := h_compat
    -- `h : (contDiffPregroupoid ω 𝓘(ℂ, ℂ)).property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source`.
    -- Unfold the pregroupoid definition and the id-shaped model-with-corners.
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      preimage_id, range_id, inter_univ] using h
  -- Break the `NormedSpace ℝ ℂ` diamond (between `NormedSpace.complexToReal`
  -- and `NormedAlgebra.toNormedSpace`) by pinning the algebra-based instance
  -- locally before the `restrict_scalars` call. Without this, the synth picks
  -- `complexToReal` and `IsScalarTower.right` cannot unify.
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact (h_fwd.of_le (le_top : n ≤ ω)).restrict_scalars ℝ

/-- **Realification of the holomorphic 1-manifold structure.**

A complex 1-manifold over `𝓘(ℂ, ℂ)` is automatically a real `C^n` manifold
over `𝓘(ℝ, ℂ)` for every regularity `n`. This is the structural prerequisite
that lets downstream chips talk about real smooth 1-forms
(`SmoothOneForm 𝓘(ℝ, ℂ) X`) on a holomorphic surface — in particular it
unblocks the period-pairing arc's PL-1, which needs to view the real and
imaginary parts of a `HolomorphicOneForm X` as bundled
`SmoothOneForm 𝓘(ℝ, ℂ) X` sections. -/
instance complexManifoldRealification
    [IsManifold 𝓘(ℂ, ℂ) ω X] {n : WithTop ℕ∞} :
    IsManifold 𝓘(ℝ, ℂ) n X := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ℂ) n X
  intro e e' he he'
  exact contDiffOn_real_chart_trans_of_complex e e' he he' n

end JacobianChallenge

end
