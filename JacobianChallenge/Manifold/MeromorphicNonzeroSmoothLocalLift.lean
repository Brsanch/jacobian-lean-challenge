/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmooth
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalPathLift
import JacobianChallenge.Manifold.ContMDiffRealification

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smoothness of the continuous local path lift at the base point

For non-constant `f.toRiemannSphere`, a `ContMDiff` path
`β : ℝ → RiemannSphere` with `β t₀ ∈ f.regularValueSet`, and a preimage
`x₀` of `β t₀`, the continuous lift `sheet.g ∘ β` (chip 11) is in fact
`ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℂ, ℂ) ω` at `t₀`.

The argument composes chip 12 (pointwise smoothness of `sheet.g` at
`f.toRiemannSphere x₀ = β t₀`) with the smoothness of `β` at `t₀` via
`ContMDiffAt.comp`.

## What ships

* `MeromorphicNonzero.contMDiffAt_local_lift_at_basepoint` — the lift
  `sheet.g ∘ β` is `ContMDiffAt ω` at `t₀`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Smooth local path lift at the base point.**

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere`,
a path `β : ℝ → RiemannSphere` smooth at `t₀` with `β t₀ ∈
f.regularValueSet`, and any preimage `x₀ ∈ f.toRiemannSphere ⁻¹' {β t₀}`,
the continuous local lift `sheet.g ∘ β` (chip 11) is
`ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℂ, ℂ) ω` at `t₀`. -/
theorem contMDiffAt_local_lift_at_basepoint
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} {t₀ : ℝ}
    (hβ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β t₀)
    (hvreg : β t₀ ∈ f.regularValueSet)
    {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      ((f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue hvreg hx₀)).g ∘ β) t₀ := by
  classical
  set hx₀_reg : x₀ ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hvreg hx₀ with hx₀_reg_def
  -- ContMDiffAt ω of sheet.g at f.toRS x₀ (chip 12).
  have h_sheet_g_omega : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (f.localSheetData_at_regular hnc hx₀_reg).g (f.toRiemannSphere x₀) :=
    f.contMDiffAt_localSheet_g_at_basePoint hnc hx₀_reg
  -- Realify: ContMDiffAt ω (complex) ⇒ ContMDiffAt ∞ (real).
  have h_sheet_g_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (f.localSheetData_at_regular hnc hx₀_reg).g (f.toRiemannSphere x₀) :=
    ContMDiffAt.complex_to_real h_sheet_g_omega
  -- Re-base at β t₀.
  have h_sheet_g' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (f.localSheetData_at_regular hnc hx₀_reg).g (β t₀) := by
    rw [← hx₀]; exact h_sheet_g_real
  -- Compose via ContMDiffAt.comp.
  exact h_sheet_g'.comp t₀ hβ

end MeromorphicNonzero

end JacobianChallenge

end
