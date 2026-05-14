/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmooth

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Open-set smoothness of the local sheet inverse near the base point

Extracts a `ContMDiffOn ω` statement on an open neighbourhood of
`v₀ = f.toRiemannSphere x₀` from chip 12's pointwise `ContMDiffAt ω`,
via mathlib's `contMDiffAt_iff_contMDiffOn_nhds` (which is valid at
regularity `ω` because `ω ≠ ∞`).

## What ships

* `MeromorphicNonzero.exists_contMDiffOn_localSheet_g_near_basePoint`
  — open neighbourhood `u ∋ v₀` and `ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
  sheet.g u`.

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

/-- **Open-nbhd `ContMDiffOn ω` of `sheet.g` near `v₀`.**

From chip 12's pointwise `ContMDiffAt ω` at `v₀ = f.toRiemannSphere x₀`,
`contMDiffAt_iff_contMDiffOn_nhds` (valid for `ω ≠ ∞`) yields an open
neighbourhood `u ∋ v₀` on which `sheet.g` is `ContMDiffOn ω`.

The membership `u ∈ 𝓝 v₀` is open-shape since 𝓝-mem-iff-supersets-an-open. -/
theorem exists_contMDiffOn_localSheet_g_near_basePoint
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀_reg : x₀ ∈ f.regularSet) :
    ∃ u : Set RiemannSphere, u ∈ 𝓝 (f.toRiemannSphere x₀) ∧
      ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (f.localSheetData_at_regular hnc hx₀_reg).g u := by
  have h_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (f.localSheetData_at_regular hnc hx₀_reg).g (f.toRiemannSphere x₀) :=
    f.contMDiffAt_localSheet_g_at_basePoint hnc hx₀_reg
  -- `ω ≠ ∞` so the iff applies.
  have hn : (ω : WithTop ℕ∞) ≠ ∞ := by decide
  exact (contMDiffAt_iff_contMDiffOn_nhds hn).mp h_at

end MeromorphicNonzero

end JacobianChallenge

end
