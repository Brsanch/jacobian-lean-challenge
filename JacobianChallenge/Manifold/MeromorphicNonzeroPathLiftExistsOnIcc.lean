/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftClosed
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftGlobalOpen

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Global continuous path lift on `Icc 0 T`

Composing **closedness** (`sSup_mem_liftReachable`) with **openness**
(`liftReachable_extends_right`) on connected `Icc 0 T`, the
`liftReachable` set fills out `Icc 0 T`: in particular `T ∈
liftReachable`, hence a globally continuous lift of `β` exists on
`Icc 0 T`.

## Argument

Let `s := sSup (liftReachable f β x₀ T)`. By closedness, `s ∈
liftReachable`. Suppose `s < T`. By openness applied at `s`, there
is `ε > 0` with `s + ε ∈ liftReachable` and `s + ε ≤ T`. But then
`s + ε ≤ sSup = s` (since `s` is an upper bound), contradicting
`ε > 0`. Hence `s ≥ T`. Combined with `s ≤ T` (`sSup_liftReachable_le`),
`s = T`, so `T ∈ liftReachable`, which unpacks to the desired
existential.

## What ships

* `MeromorphicNonzero.sSup_liftReachable_eq_T` — `sSup = T`.
* `MeromorphicNonzero.exists_continuous_lift_on_Icc` — headline
  existence of a continuous lift on `Icc 0 T`.

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

/-- **`sSup (liftReachable) = T`.**

Closedness + openness + `0 ∈ liftReachable` force `sSup` to reach
`T`. Strict inequality `sSup < T` is ruled out by `liftReachable_extends_right`
producing a strictly larger element. -/
theorem sSup_liftReachable_eq_T
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β) (x₀ : X)
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    (hx₀ : f.toRiemannSphere x₀ = β 0) (hT : 0 ≤ T) :
    sSup (f.liftReachable β x₀ T) = T := by
  classical
  set s := sSup (f.liftReachable β x₀ T) with hs_def
  have h_s_le : s ≤ T := f.sSup_liftReachable_le hx₀ hT
  -- It suffices to show ¬ s < T.
  refine le_antisymm h_s_le ?_
  by_contra h_not
  push Not at h_not
  -- h_not : s < T. Closedness + openness contradict.
  have h_s_mem : s ∈ f.liftReachable β x₀ T :=
    f.sSup_mem_liftReachable hnc hβ_cont x₀ hβ_reg hx₀ hT
  obtain ⟨ε, hε_pos, _hε_le, h_s_plus_mem⟩ :=
    f.liftReachable_extends_right hnc hβ_cont hβ_reg h_s_mem h_not
  have h_bdd : BddAbove (f.liftReachable β x₀ T) :=
    f.liftReachable_bddAbove β x₀ T
  have h_s_plus_le : s + ε ≤ s := by
    have : s + ε ≤ sSup (f.liftReachable β x₀ T) :=
      le_csSup h_bdd h_s_plus_mem
    rwa [← hs_def] at this
  linarith

/-- **Global continuous lift on `Icc 0 T`.**

For non-constant `f.toRiemannSphere`, a continuous `β` taking regular
values on `Icc 0 T`, and a base preimage `x₀` over `β 0`, there is a
continuous `γ : ℝ → X` with `γ 0 = x₀` and `f.toRiemannSphere ∘ γ = β`
on `Icc 0 T`. -/
theorem exists_continuous_lift_on_Icc
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β) (x₀ : X)
    {T : ℝ}
    (hβ_reg : ∀ t ∈ Icc 0 T, β t ∈ f.regularValueSet)
    (hx₀ : f.toRiemannSphere x₀ = β 0) (hT : 0 ≤ T) :
    ∃ γ : ℝ → X, Continuous γ ∧ γ 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, f.toRiemannSphere (γ t) = β t := by
  -- `T = sSup ∈ liftReachable`, so unfolding `liftReachable` produces γ.
  have h_eq : sSup (f.liftReachable β x₀ T) = T :=
    f.sSup_liftReachable_eq_T hnc hβ_cont x₀ hβ_reg hx₀ hT
  have h_s_mem : sSup (f.liftReachable β x₀ T) ∈ f.liftReachable β x₀ T :=
    f.sSup_mem_liftReachable hnc hβ_cont x₀ hβ_reg hx₀ hT
  -- Unpack: lift exists over Icc 0 sSup. Since sSup = T, that's Icc 0 T.
  obtain ⟨_, γ, hγ_cont, hγ_zero, hγ_lift⟩ := h_s_mem
  refine ⟨γ, hγ_cont, hγ_zero, ?_⟩
  intro t ht
  apply hγ_lift t
  rw [h_eq]; exact ht

end MeromorphicNonzero

end JacobianChallenge

end
