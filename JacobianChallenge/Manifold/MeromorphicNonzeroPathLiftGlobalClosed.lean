/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftGlobalOpen
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Boundedness of `liftReachable`

The set `liftReachable` is bounded above by `T` and bounded below by
`0`.  This means its supremum exists in `Icc 0 T` (with the usual
`sSup` conventions when non-empty).

This file ships the boundedness lemmas; the substantive closedness
(`sSup ∈ liftReachable`) requires sequential limits and a local-sheet
limit argument — separate chip.

## What ships

* `MeromorphicNonzero.liftReachable_subset_Icc` — `liftReachable ⊆
  Icc 0 T`.
* `MeromorphicNonzero.liftReachable_bddAbove` — bounded above by `T`.
* `MeromorphicNonzero.sSup_liftReachable_le` — `sSup ≤ T`.
* `MeromorphicNonzero.sSup_liftReachable_nonneg` — `0 ≤ sSup`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- `liftReachable ⊆ Icc 0 T`. -/
lemma liftReachable_subset_Icc
    (f : MeromorphicNonzero X) (β : ℝ → RiemannSphere) (x₀ : X) (T : ℝ) :
    f.liftReachable β x₀ T ⊆ Icc 0 T := by
  intro b hb; exact hb.1

/-- `liftReachable` is bounded above by `T`. -/
lemma liftReachable_bddAbove
    (f : MeromorphicNonzero X) (β : ℝ → RiemannSphere) (x₀ : X) (T : ℝ) :
    BddAbove (f.liftReachable β x₀ T) :=
  ⟨T, fun _ hb => hb.1.2⟩

/-- `sSup (liftReachable) ≤ T`. -/
lemma sSup_liftReachable_le
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere} {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β 0)
    {T : ℝ} (hT : 0 ≤ T) :
    sSup (f.liftReachable β x₀ T) ≤ T := by
  refine csSup_le ⟨0, f.zero_mem_liftReachable hx₀ hT⟩ ?_
  intro b hb; exact hb.1.2

/-- `0 ≤ sSup (liftReachable)`. -/
lemma sSup_liftReachable_nonneg
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere} {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β 0)
    {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ sSup (f.liftReachable β x₀ T) :=
  le_csSup (f.liftReachable_bddAbove β x₀ T)
    (f.zero_mem_liftReachable hx₀ hT)

end MeromorphicNonzero

end JacobianChallenge

end
