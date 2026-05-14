/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import JacobianChallenge.Manifold.ComplexManifoldRealification

set_option linter.unusedSectionVars false

/-! # Function-level realification of `ContMDiff` between complex 1-manifolds

The function-level analog of `JacobianChallenge.complexManifoldRealification`:
if `f : X → Y` is holomorphic between complex 1-manifolds
(`ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f`), then `f` is C^∞ as a map between the
realifications (`ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f`).

The chart-coordinate characterisation `contMDiffAt_iff` reduces both
predicates to a `ContDiffWithinAt 𝕜 n (chart-pullback) (range I) (chart x)`
statement, where the chart-pullback function and the membership `range I
= univ` agree across the two models (both `𝓘(ℂ, ℂ)` and `𝓘(ℝ, ℂ)` are
boundaryless self-id models on `ℂ`). Only the scalar field `𝕜` differs:
ℂ vs ℝ. The conversion is then
`ContDiffWithinAt.restrict_scalars` (drop ℂ → ℝ) followed by
`ContDiffWithinAt.of_le` (drop ω → ∞ regularity).

Together with `complexManifoldRealification` (typeclass instance) and
`ContMDiff.compSmoothPath` / `SmoothChain.compSmoothMap`, this lemma lets
us pushforward smooth paths and chains through holomorphic maps such as
`MeromorphicNonzero.toRiemannSphere` (which is `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω`),
unblocking the level-set chain construction toward Abel forward.

No `sorry`, no `axiom`.
-/

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Pointwise realification of `ContMDiffAt`.** A holomorphic map at
`x` is C^∞-real at `x` (real model, boundaryless self-id on `ℂ`). -/
theorem ContMDiffAt.complex_to_real {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f x) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x := by
  -- Reduce both sides via `contMDiffAt_iff`.
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨h_cont, h_diff⟩ := hf
  refine ⟨h_cont, ?_⟩
  -- Both `extChartAt 𝓘(ℂ,ℂ) ·` and `extChartAt 𝓘(ℝ,ℂ) ·` reduce to
  -- `chartAt ℂ ·` (as functions) because both models are the identity
  -- self-id model on `ℂ`. `range 𝓘(ℂ, ℂ) = range 𝓘(ℝ, ℂ) = univ`
  -- (boundaryless self). The only difference is the scalar field in
  -- the `ContDiffWithinAt`.
  have h_range_c : range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ := by
    simp [ModelWithCorners.range_eq_univ]
  have h_range_r : range (𝓘(ℝ, ℂ) : ModelWithCorners ℝ ℂ ℂ) = univ := by
    simp [ModelWithCorners.range_eq_univ]
  -- The two `extChartAt`s as functions are equal modulo
  -- `modelWithCornersSelf_coe`.
  have h_ext_eq_c : ⇑(extChartAt (𝓘(ℂ, ℂ)) x) = ⇑(chartAt ℂ x) := by
    ext z; simp [extChartAt_coe]
  have h_ext_eq_c_y : ⇑(extChartAt (𝓘(ℂ, ℂ)) (f x)) = ⇑(chartAt ℂ (f x)) := by
    ext z; simp [extChartAt_coe]
  have h_ext_symm_c : ⇑(extChartAt (𝓘(ℂ, ℂ)) x).symm = ⇑(chartAt ℂ x).symm := by
    ext z; simp [extChartAt_coe_symm]
  have h_ext_eq_r : ⇑(extChartAt (𝓘(ℝ, ℂ)) x) = ⇑(chartAt ℂ x) := by
    ext z; simp [extChartAt_coe]
  have h_ext_eq_r_y : ⇑(extChartAt (𝓘(ℝ, ℂ)) (f x)) = ⇑(chartAt ℂ (f x)) := by
    ext z; simp [extChartAt_coe]
  have h_ext_symm_r : ⇑(extChartAt (𝓘(ℝ, ℂ)) x).symm = ⇑(chartAt ℂ x).symm := by
    ext z; simp [extChartAt_coe_symm]
  -- Rewrite the chart-pullback function on both sides.
  rw [h_range_r, h_ext_eq_r, h_ext_eq_r_y, h_ext_symm_r]
  rw [h_range_c, h_ext_eq_c, h_ext_eq_c_y, h_ext_symm_c] at h_diff
  -- Now `h_diff : ContDiffWithinAt ℂ ω (chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm) univ ((chartAt ℂ x) x)`.
  -- Goal: same predicate but with ℝ ∞ in place of ℂ ω.
  -- Break the `NormedSpace ℝ ℂ` diamond (between `NormedSpace.complexToReal`
  -- and `NormedAlgebra.toNormedSpace`) by pinning the algebra-based instance
  -- locally before the `restrict_scalars` call. Without this, the synth picks
  -- `complexToReal` and `IsScalarTower.right` cannot unify. Cribbed from
  -- `Manifold/ComplexManifoldRealification.lean`'s
  -- `contDiffOn_real_chart_trans_of_complex`.
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  have h_real : ContDiffWithinAt ℝ ω
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) univ ((chartAt ℂ x) x) :=
    ContDiffWithinAt.restrict_scalars (𝕜 := ℝ) h_diff
  exact h_real.of_le (by decide)

/-- **Realification of `ContMDiff`.** Function-level upgrade: a
holomorphic map is C^∞-real-smooth between the realified manifold
structures. -/
theorem ContMDiff.complex_to_real {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := by
  intro x
  have hat : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f x := hf x
  exact ContMDiffAt.complex_to_real hat

end JacobianChallenge

end
