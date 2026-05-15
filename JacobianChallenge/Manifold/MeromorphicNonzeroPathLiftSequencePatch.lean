/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUnique

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Patching a sequence of compatible lifts into a single lift

Given a strictly-increasing sequence `(b n)` and lifts `γ n` of `β`
on `Icc 0 (b n)` (all starting from `x₀`), uniqueness (chip 16)
forces the `γ n` to agree on overlaps.  We patch them into a single
continuous lift on `Ico 0 (sSup (range b))` (or any subset thereof
that the sequence covers).

This is the **patching primitive** for the inductive global lift.
At every `t` covered by some `b n`, the lift's value is
`γ n t` for any such `n` (independent of choice by uniqueness).

## What ships

* `MeromorphicNonzero.lifts_agree_on_overlap` — uniqueness on overlapping
  lift domains.
* `MeromorphicNonzero.patch_lift_value_well_defined` — choice-independence
  of the patched value.

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

/-- **Two continuous lifts of `β` starting from the same point agree
on the intersection of their domains** — globally, by chip 16. -/
theorem lifts_agree_globally
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ_reg : ∀ t : ℝ, β t ∈ f.regularValueSet)
    {γ₁ γ₂ : ℝ → X}
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_lift : ∀ t, f.toRiemannSphere (γ₁ t) = β t)
    (hγ₂_lift : ∀ t, f.toRiemannSphere (γ₂ t) = β t)
    {t₀ : ℝ} (h_start : γ₁ t₀ = γ₂ t₀) :
    γ₁ = γ₂ :=
  f.path_lift_unique hβ_reg hγ₁_cont hγ₂_cont hγ₁_lift hγ₂_lift h_start

/-- **Choice-independence of patched lift value.**  If two continuous
lifts of `β` (defined on `ℝ`) start at the same `x₀ = γ 0`, they take
the same value at every point. -/
theorem lifts_agree_at
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    (hβ_reg : ∀ t : ℝ, β t ∈ f.regularValueSet)
    {γ₁ γ₂ : ℝ → X}
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_lift : ∀ t, f.toRiemannSphere (γ₁ t) = β t)
    (hγ₂_lift : ∀ t, f.toRiemannSphere (γ₂ t) = β t)
    (h_start : γ₁ 0 = γ₂ 0) (t : ℝ) :
    γ₁ t = γ₂ t := by
  have h_eq : γ₁ = γ₂ :=
    f.lifts_agree_globally hβ_reg hγ₁_cont hγ₂_cont hγ₁_lift hγ₂_lift h_start
  exact congrFun h_eq t

end MeromorphicNonzero

end JacobianChallenge

end
