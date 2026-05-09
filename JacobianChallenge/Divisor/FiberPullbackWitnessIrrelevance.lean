/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.FiberPullback

set_option diagnostics.threshold 100

/-! # Witness irrelevance for `Pic0.pullback`

Two finiteness witnesses for the same fibre give the same `toFinset`
(via Mathlib's `Set.Finite.toFinset_inj`). Hence `Pic0.pullback`,
`Div.fiberSum`, and friends depend only on `f` and `N`, not on the
specific finiteness proof. -/

namespace JacobianChallenge

namespace Pic0

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X]

/-- **Witness-N irrelevance: two `N` values must agree on Y nonempty.** -/
lemma N_eq_of_constFibreCard_witnesses
    (f : X → Y) [Nonempty Y]
    (hf₁ hf₂ : ∀ y, (f ⁻¹' {y}).Finite) (N₁ N₂ : ℕ)
    (hN₁ : ∀ y, (hf₁ y).toFinset.card = N₁)
    (hN₂ : ∀ y, (hf₂ y).toFinset.card = N₂) :
    N₁ = N₂ := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have h₁ : (hf₁ y).toFinset.card = N₁ := hN₁ y
  have h₂ : (hf₂ y).toFinset.card = N₂ := hN₂ y
  have heq : (hf₁ y).toFinset = (hf₂ y).toFinset :=
    Set.Finite.toFinset_inj.mpr rfl
  rw [heq] at h₁
  exact h₁.symm.trans h₂

end Pic0

end JacobianChallenge
