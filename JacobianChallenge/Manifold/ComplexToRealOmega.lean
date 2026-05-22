/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ContMDiffRealification
import JacobianChallenge.Manifold.ComplexManifoldRealification

set_option linter.unusedSectionVars false

/-! # ω-level real-side realification of holomorphic maps

`ContMDiff.complex_to_real` in `ContMDiffRealification.lean` outputs at
`∞ : WithTop ℕ∞` (it ends with `.of_le (by decide)` from an underlying
`ContDiffWithinAt ℝ ω`). This file exposes the analytic-level variant
`ContMDiff.complex_to_real_omega` that does not drop the regularity.

It's the bridge needed to feed real-side smoothness into
`SmoothOneForm.pullback` (which requires `ω`-smooth `f`).

Proof: same chart-coordinate reduction as `complex_to_real`, but on the
final `.restrict_scalars` we don't compose with `.of_le`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **ω-level real-side realification (pointwise).** Same shape as
`ContMDiffAt.complex_to_real` but lands at `ω` rather than `∞`. -/
theorem ContMDiffAt.complex_to_real_omega {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f x) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω f x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨h_cont, h_diff⟩ := hf
  refine ⟨h_cont, ?_⟩
  have h_range_c : range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ := by
    simp [ModelWithCorners.range_eq_univ]
  have h_range_r : range (𝓘(ℝ, ℂ) : ModelWithCorners ℝ ℂ ℂ) = univ := by
    simp [ModelWithCorners.range_eq_univ]
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
  rw [h_range_r, h_ext_eq_r, h_ext_eq_r_y, h_ext_symm_r]
  rw [h_range_c, h_ext_eq_c, h_ext_eq_c_y, h_ext_symm_c] at h_diff
  -- Break the `NormedSpace ℝ ℂ` diamond by pinning the algebra-based instance.
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact h_diff.restrict_scalars ℝ

/-- **ω-level real-side realification (global).** -/
theorem ContMDiff.complex_to_real_omega {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω f := fun x =>
  ContMDiffAt.complex_to_real_omega (hf x)

end JacobianChallenge

end
