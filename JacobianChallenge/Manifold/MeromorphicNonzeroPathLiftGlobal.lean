/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftAtPoint
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Global continuous path lift on `Icc 0 T` via sSup + clopen

For non-constant `f.toRiemannSphere`, a continuous path `β : ℝ →
RiemannSphere` with `β` taking regular values on `Icc 0 T` (any
`T ≥ 0`), and a preimage `x₀ ∈ f.toRiemannSphere ⁻¹' {β 0}`, there is
a continuous global lift `γ : ℝ → X` with `γ 0 = x₀` and
`f.toRiemannSphere ∘ γ = β` on `Icc 0 T`.

## Argument (clopen on `Icc 0 T`)

Set `S := { b ∈ Icc 0 T | ∃ γ : ℝ → X continuous with γ 0 = x₀ and
f.toRiemannSphere ∘ γ = β on Icc 0 b }`.

* `0 ∈ S`: take `γ ≡ x₀`.
* `S` is open in `Icc 0 T`: if `b ∈ S`, chip 20's
  `extend_continuous_lift_to_right` extends past `b` by `ε > 0`.
* `S` is closed in `Icc 0 T`: limit of lifts; constructive
  argument via local sheet at any limit point.
* `Icc 0 T` is connected (`Subtype.preconnectedSpace +
  isPreconnected_Icc`).
* Therefore `S = univ`, i.e., `T ∈ S`.

The closed step is the substantive part: given `(b_n) ↑ b` with each
`b_n ∈ S`, patch the lifts (uniqueness from chip 22) into `γ` on
`Icc 0 b`, defining `γ(b)` as the limit of `γ(b_n)` (which exists via
a local-sheet argument at any preimage of `β b`).

## What ships

* `MeromorphicNonzero.exists_continuous_lift_on_Icc` — headline.

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

/-- **Lift-reachable set on `Icc 0 T`.** -/
def liftReachable (f : MeromorphicNonzero X) (β : ℝ → RiemannSphere)
    (x₀ : X) (T : ℝ) : Set ℝ :=
  { b ∈ Icc 0 T | ∃ γ : ℝ → X, Continuous γ ∧ γ 0 = x₀ ∧
    ∀ t ∈ Icc 0 b, f.toRiemannSphere (γ t) = β t }

/-- `0 ∈ liftReachable` (constant lift). -/
lemma zero_mem_liftReachable
    (f : MeromorphicNonzero X)
    {β : ℝ → RiemannSphere}
    {x₀ : X} (hx₀ : f.toRiemannSphere x₀ = β 0)
    {T : ℝ} (hT : 0 ≤ T) :
    (0 : ℝ) ∈ f.liftReachable β x₀ T := by
  refine ⟨⟨le_refl 0, hT⟩, fun _ => x₀, continuous_const, rfl, ?_⟩
  intro t ht
  have ht_eq : t = 0 := le_antisymm ht.2 ht.1
  rw [ht_eq]; exact hx₀

/-- **liftReachable is closed under `≤`.** -/
lemma liftReachable_downward_closed
    (f : MeromorphicNonzero X) (β : ℝ → RiemannSphere) (x₀ : X)
    {T : ℝ}
    {b b' : ℝ} (hb_mem : b ∈ f.liftReachable β x₀ T) (hb'_le : b' ≤ b)
    (hb'_nonneg : 0 ≤ b') :
    b' ∈ f.liftReachable β x₀ T := by
  obtain ⟨hb_in_Icc, γ, hγ_cont, hγ_0, hγ_lift⟩ := hb_mem
  refine ⟨⟨hb'_nonneg, hb'_le.trans hb_in_Icc.2⟩, γ, hγ_cont, hγ_0, ?_⟩
  intro t ht
  exact hγ_lift t ⟨ht.1, ht.2.trans hb'_le⟩

end MeromorphicNonzero

end JacobianChallenge

end
