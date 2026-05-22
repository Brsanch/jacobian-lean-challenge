/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # `IsManifold (𝓘(ℝ, ℂ)) ∞ X` from `IsManifold (𝓘(ℂ, ℂ)) ω X`

A `ChartedSpace ℂ X` carrying `IsManifold (𝓘(ℂ, ℂ)) ω X` (holomorphic
manifold structure) also carries `IsManifold (𝓘(ℝ, ℂ)) ∞ X` (smooth
ℝ-model structure on the same chart family): the chart transitions
are ℂ-analytic on their source, hence ℝ-`C^∞`-smooth.

## The diamond workaround

The naive derivation `ContDiffOn ℂ ω f s → ContDiffOn ℝ ∞ f s`
(`f : ℂ → ℂ`) via `ContDiffOn.restrict_scalars ℝ` requires
`IsScalarTower ℝ ℂ ℂ`. At this mathlib pin, the typeclass synthesizer
at the `restrict_scalars` call site cannot resolve that instance —
even though it succeeds in isolation. Cause: the
`Complex.SMul.instSMulRealComplex` vs `Algebra.id ℂ`-SMul diamond
flagged in `memory/feedback_jacobian_complex_real_diamond.md`.

Workaround: `set_option backward.isDefEq.respectTransparency false`
(the same trick mathlib uses for `StarModule.complexToReal` in
`LinearAlgebra/Complex/Module.lean:204`). With that option, the
typeclass resolution navigates past the diamond.

No `sorry`, no `axiom`. -/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff
open Set

namespace JacobianChallenge

/-- **Diamond-aware bridge** `ContDiffOn ℂ ω → ContDiffOn ℝ ∞` for
`ℂ → ℂ` functions. Uses the file-scope `respectTransparency false`
option to break the `IsScalarTower ℝ ℂ ℂ` diamond. -/
theorem contDiffOn_real_top_of_contDiffOn_complex_omega
    {s : Set ℂ} {f : ℂ → ℂ} (h : ContDiffOn ℂ ω f s) :
    ContDiffOn ℝ ∞ f s :=
  (h.of_le le_top).restrict_scalars ℝ

/-! ## The IsManifold instance -/

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`IsManifold (𝓘(ℝ, ℂ)) ∞ X` from `IsManifold (𝓘(ℂ, ℂ)) ω X`.**

The chart transitions of `X` viewed via `𝓘(ℝ, ℂ)` are `ContDiffOn ℝ ∞`
on their source, because they're `ContDiffOn ℂ ω` (from the
holomorphic instance) and the diamond-aware bridge above gives the
field restriction. -/
instance instIsManifoldRealComplexOfComplexAnalytic :
    IsManifold (𝓘(ℝ, ℂ)) ∞ X := by
  refine isManifold_of_contDiffOn _ ∞ X ?_
  intro e e' he he'
  -- Chart transition for the ℂ-analytic atlas → ContDiffOn ℂ ω.
  have h_compat : e.symm ≫ₕ e' ∈ contDiffGroupoid ω 𝓘(ℂ, ℂ) :=
    HasGroupoid.compatible he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h_compat
  have hℂω : ContDiffOn ℂ ω
      (𝓘(ℂ, ℂ) ∘ (e.symm ≫ₕ e' : OpenPartialHomeomorph ℂ ℂ) ∘ 𝓘(ℂ, ℂ).symm)
      (𝓘(ℂ, ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range 𝓘(ℂ, ℂ)) :=
    h_compat.1
  -- 𝓘(ℂ, ℂ) and 𝓘(ℝ, ℂ) both unfold to identity functions on ℂ,
  -- and range = univ, so the underlying ContDiffOn statements coincide
  -- up to model wrapper unfolds.
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    CompTriple.comp_eq, preimage_id_eq, id_eq, range_id,
    inter_univ] at hℂω ⊢
  -- Bridge ℂω → ℝ∞.
  exact contDiffOn_real_top_of_contDiffOn_complex_omega hℂω

end JacobianChallenge
