/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalPathLift
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Global continuous lift on a single sheet

If the entire image `β '' unitInterval` lies in the `V`-set of a single
`LocalSheetData` (built from some regular anchor `x_anchor`), and the
initial preimage `x₀ = β 0`-lift lies in the sheet's `U`-set, then
`sheet.g ∘ β` is a continuous global lift of `β` on `ℝ`, agreeing with
`β` via `f.toRiemannSphere` everywhere `β` lands in `V`.

This is the **single-sheet** case of the global path lift: no gluing
is needed when one local sheet covers the entire path image. The
general case (chip 19) glues finitely many single-sheet lifts via
the partition from chip 17.

## What ships

* `MeromorphicNonzero.exists_continuous_lift_single_sheet` — global
  continuous lift in the single-sheet case.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Topology Manifold ContDiff unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Global continuous path lift on a single sheet.**

If β's image (everywhere on `ℝ`) lies in the local sheet's `V`-set,
and `x₀` is in the sheet's `U`-set with `f.toRiemannSphere x₀ = β 0`,
then `γ := sheet.g ∘ β` is a continuous global lift of `β`. -/
theorem exists_continuous_lift_single_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    {x_anchor : X} (hx_anchor_reg : x_anchor ∈ f.regularSet)
    (hβ_in_V : ∀ t : ℝ, β t ∈ (f.localSheetData_at_regular hnc hx_anchor_reg).V)
    {x₀ : X}
    (hx₀_in_U : x₀ ∈ (f.localSheetData_at_regular hnc hx_anchor_reg).U)
    (hx₀ : f.toRiemannSphere x₀ = β 0) :
    ∃ γ : ℝ → X, Continuous γ ∧ γ 0 = x₀ ∧
      ∀ t : ℝ, f.toRiemannSphere (γ t) = β t := by
  classical
  set sheet := f.localSheetData_at_regular hnc hx_anchor_reg with hsheet_def
  refine ⟨sheet.g ∘ β, ?_, ?_, ?_⟩
  · -- Continuity: ContinuousOn sheet.g sheet.V + β maps into sheet.V.
    have h_cont_on : ContinuousOn sheet.g sheet.V := sheet.g_continuousOn
    have h_mapsTo : MapsTo β univ sheet.V := fun t _ => hβ_in_V t
    -- Continuity of composition on univ.
    have h_univ_cont : ContinuousOn (sheet.g ∘ β) univ := by
      refine h_cont_on.comp hβ_cont.continuousOn h_mapsTo
    rwa [continuousOn_univ] at h_univ_cont
  · -- γ 0 = x₀.
    show (sheet.g ∘ β) 0 = x₀
    rw [Function.comp_apply, ← hx₀]
    exact sheet.leftInvOn hx₀_in_U
  · -- f.toRiemannSphere (γ t) = β t.
    intro t
    show f.toRiemannSphere (sheet.g (β t)) = β t
    exact sheet.rightInvOn (hβ_in_V t)

end MeromorphicNonzero

end JacobianChallenge

end
