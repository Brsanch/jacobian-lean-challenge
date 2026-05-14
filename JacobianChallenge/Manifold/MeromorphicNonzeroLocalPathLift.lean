/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import Mathlib.Topology.UnitInterval

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Continuous local path lift through regular values

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere`,
a continuous path `β : ℝ → RiemannSphere` (or `C(I, RiemannSphere)`),
and a preimage `x₀ ∈ f.toRiemannSphere ⁻¹' {β t₀}` of a value lying in
`f.regularValueSet`, the local sheet at `x₀` (chip 7) gives a
continuous inverse `g` on an open neighbourhood of `β t₀`.  By
continuity of `β`, an open neighbourhood of `t₀` in `ℝ` has its image
under `β` contained in this neighbourhood, so `γ t := g (β t)` is a
continuous local lift of `β` near `t₀` with `γ t₀ = x₀`.

This is the *local* form of the path lifting theorem on the covering
`f.toRiemannSphere : f.toRiemannSphere ⁻¹' f.regularValueSet →
f.regularValueSet`.  The *global* lift on the full unit interval
requires gluing via compactness — separate chip.

## What ships

* `MeromorphicNonzero.exists_continuous_local_lift_of_continuous_at` —
  for `β : ℝ → RiemannSphere` continuous at `t₀` with `β t₀ ∈
  f.regularValueSet`, the existence of an open `W ⊆ ℝ` containing `t₀`,
  a continuous local lift `γ : ℝ → X`, and the inversion property
  `f.toRiemannSphere (γ t) = β t` on `W`.

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

/-- **Continuous local path lift at a regular preimage.**

For a path `β : ℝ → RiemannSphere` continuous at `t₀` with `β t₀ ∈
f.regularValueSet`, and any preimage `x₀ ∈ f.toRiemannSphere ⁻¹' {β t₀}`,
there is an open neighbourhood `W ⊆ ℝ` of `t₀` and a continuous local
lift `γ : ℝ → X` with `γ t₀ = x₀` and `f.toRiemannSphere (γ t) = β t`
for all `t ∈ W`.

Construction:
* From `β t₀ ∈ f.regularValueSet` and `f.toRiemannSphere x₀ = β t₀`,
  conclude `x₀ ∈ f.regularSet`.
* Build the manifold local sheet at `x₀` (chip 7).
* The sheet supplies a continuous `g : RiemannSphere → X` on an open
  `V_x₀ ∋ β t₀` with `g ∘ f.toRiemannSphere = id` on `U_x₀` and
  `f.toRiemannSphere ∘ g = id` on `V_x₀`.
* Set `γ := g ∘ β`. By continuity of `β` at `t₀`, the preimage `β ⁻¹'
  V_x₀` is a neighbourhood of `t₀`; take its interior `W` for openness.
-/
theorem exists_continuous_local_lift_of_continuous
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} {t₀ : ℝ}
    (hβ : Continuous β)
    (hvreg : β t₀ ∈ f.regularValueSet)
    {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β t₀) :
    ∃ W : Set ℝ, IsOpen W ∧ t₀ ∈ W ∧
      ∃ γ : ℝ → X, ContinuousOn γ W ∧
        γ t₀ = x₀ ∧
        ∀ t ∈ W, f.toRiemannSphere (γ t) = β t := by
  classical
  -- x₀ is regular (preimage of a regular value).
  have hx₀_reg : x₀ ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hvreg hx₀
  -- Manifold local sheet at x₀.
  set sheet := f.localSheetData_at_regular hnc hx₀_reg with hsheet_def
  -- sheet.V ∋ f.toRiemannSphere x₀ = β t₀, sheet.V is open.
  have hVopen : IsOpen sheet.V := sheet.V_open
  have hmemV : β t₀ ∈ sheet.V := by
    rw [← hx₀]; exact sheet.mem_V
  -- β⁻¹' sheet.V is open in ℝ (preimage of open under continuous β).
  have hW_open : IsOpen (β ⁻¹' sheet.V) := hVopen.preimage hβ
  have ht₀_W : t₀ ∈ β ⁻¹' sheet.V := hmemV
  refine ⟨β ⁻¹' sheet.V, hW_open, ht₀_W, sheet.g ∘ β, ?_, ?_, ?_⟩
  · -- ContinuousOn (sheet.g ∘ β) (β⁻¹' sheet.V).
    -- sheet.g_continuousOn : ContinuousOn sheet.g sheet.V.
    -- β globally continuous + MapsTo β (β⁻¹' sheet.V) sheet.V gives the
    -- composition continuity via ContinuousOn.comp.
    refine ContinuousOn.comp sheet.g_continuousOn hβ.continuousOn ?_
    intro t ht
    exact ht
  · -- γ t₀ = x₀.
    show (sheet.g ∘ β) t₀ = x₀
    rw [Function.comp_apply, ← hx₀]
    exact sheet.leftInvOn sheet.mem_U
  · -- f.toRiemannSphere (sheet.g (β t)) = β t.
    intro t htW
    show f.toRiemannSphere (sheet.g (β t)) = β t
    exact sheet.rightInvOn htW

end MeromorphicNonzero

end JacobianChallenge

end
