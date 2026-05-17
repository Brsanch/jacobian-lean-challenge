/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveLinear
import JacobianChallenge.Manifold.PrimitiveSubsingletonReduction

set_option linter.unusedSectionVars false

/-! # Factoring `LoopPeriodVanishes` through a basis

By ℂ-linearity of `complexChainPeriod` in the form argument, the named
hypothesis `LoopPeriodVanishes om x₀` is preserved under ℂ-linear
combinations of forms. Therefore, given a ℂ-basis of
`HolomorphicOneForm X` (available unconditionally via item 1's
`HolomorphicOneFormFiniteDim`), checking `LoopPeriodVanishes` on each
basis element suffices.

This reduces `AllLoopsVanish` (a quantifier over all forms) to a finite
disjunctive check — at most `genus X` named inputs, one per basis
element.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- `LoopPeriodVanishes` of the zero form is trivial. -/
theorem loopPeriodVanishes_zero (x₀ : X) :
    LoopPeriodVanishes (0 : HolomorphicOneForm X) x₀ := by
  intro γ _ _
  rw [complexChainPeriod_zero_right]

/-- `LoopPeriodVanishes` is preserved by addition. -/
theorem loopPeriodVanishes_add {om₁ om₂ : HolomorphicOneForm X} {x₀ : X}
    (h₁ : LoopPeriodVanishes om₁ x₀) (h₂ : LoopPeriodVanishes om₂ x₀) :
    LoopPeriodVanishes (om₁ + om₂) x₀ := by
  intro γ h_src h_tgt
  rw [complexChainPeriod_add_right]
  rw [h₁ γ h_src h_tgt, h₂ γ h_src h_tgt]
  ring

/-- `LoopPeriodVanishes` is preserved by ℂ-scaling. -/
theorem loopPeriodVanishes_smul (z : ℂ) {om : HolomorphicOneForm X} {x₀ : X}
    (h : LoopPeriodVanishes om x₀) :
    LoopPeriodVanishes (z • om) x₀ := by
  intro γ h_src h_tgt
  rw [complexChainPeriod_smul_complex_right]
  rw [h γ h_src h_tgt]
  ring

/-- `LoopPeriodVanishes` is preserved by negation. -/
theorem loopPeriodVanishes_neg {om : HolomorphicOneForm X} {x₀ : X}
    (h : LoopPeriodVanishes om x₀) :
    LoopPeriodVanishes (-om) x₀ := by
  intro γ h_src h_tgt
  rw [complexChainPeriod_neg_right]
  rw [h γ h_src h_tgt]
  ring

/-- **`LoopPeriodVanishes` extends from a ℂ-spanning set to all forms.**
If every element of a ℂ-spanning set `S ⊆ HolomorphicOneForm X` satisfies
`LoopPeriodVanishes`, then so does every form in `HolomorphicOneForm X`. -/
theorem loopPeriodVanishes_of_spanning
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    {S : Set (HolomorphicOneForm X)} (h_span : Submodule.span ℂ S = ⊤)
    {x₀ : X} (h_S : ∀ om ∈ S, LoopPeriodVanishes om x₀) :
    ∀ om : HolomorphicOneForm X, LoopPeriodVanishes om x₀ := by
  intro om
  have hmem : om ∈ Submodule.span ℂ S := by rw [h_span]; trivial
  -- Use Submodule.span induction.
  refine Submodule.span_induction (p := fun v _ => LoopPeriodVanishes v x₀)
    (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hmem
  · intros v hv; exact h_S v hv
  · exact loopPeriodVanishes_zero x₀
  · intros v₁ v₂ _ _ hv₁ hv₂
    exact loopPeriodVanishes_add hv₁ hv₂
  · intros c v _ hv
    exact loopPeriodVanishes_smul c hv

/-- **`AllLoopsVanish` reduces to a basis-wise check.** Given a ℂ-basis,
checking `LoopPeriodVanishes` at each basis element suffices. -/
theorem allLoopsVanish_of_basis
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    {ι : Type*} (b : Basis ι ℂ (HolomorphicOneForm X)) {x₀ : X}
    (h_b : ∀ i, LoopPeriodVanishes (b i) x₀) :
    AllLoopsVanish (X := X) x₀ := by
  unfold AllLoopsVanish
  apply loopPeriodVanishes_of_spanning b.span_eq
  rintro _ ⟨i, rfl⟩
  exact h_b i

end JacobianChallenge

end
