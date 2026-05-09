/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.FiberPullback

set_option diagnostics.threshold 100

/-! # Witness irrelevance for `Pic0.pullback`

For a fixed `f : X → Y`, the value of `Pic0.pullback f hf N hN P`
depends only on `f`, `N`, and `P` — not on the specific finiteness
proof `hf` or the per-fibre cardinality proof `hN`. This is because:

1. Two `Set.Finite` proofs of the same set give the same `.toFinset`
   (by Finset extensionality on the underlying set).
2. The `divPullback` construction reads only the toFinset of each fibre
   plus the value `N`.

Combined with the existence of a constant-fibre witness, this lets us
state and use `Pic0.pullback` via `Classical.choose`-extracted
witnesses while preserving extensional equality.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

namespace Pic0

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X]

/-- **Witness irrelevance for fibre toFinset.** Two finiteness proofs of
the same set produce equal `toFinset` values. -/
lemma _root_.Set.Finite.toFinset_eq_of_set_eq
    {α : Type*} [DecidableEq α]
    {S T : Set α} (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
    hS.toFinset = hT.toFinset := by
  ext a
  simp [Set.Finite.mem_toFinset, hST]

/-- **Witness irrelevance for `Div.fiberSum`.** -/
lemma _root_.JacobianChallenge.Div.fiberSum_eq_of_witness_irrelevance
    (f : X → Y) (hf₁ hf₂ : ∀ y, (f ⁻¹' {y}).Finite) (D : Div Y) :
    Div.fiberSum f hf₁ D = Div.fiberSum f hf₂ D := by
  classical
  show Div.fiberSumFun f hf₁ D = Div.fiberSumFun f hf₂ D
  unfold Div.fiberSumFun
  refine Finset.sum_congr rfl ?_
  intro y _
  congr 1
  -- Inner sum over (hf y).toFinset, with same underlying set.
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  exact Set.Finite.toFinset_eq_of_set_eq (hf₁ y) (hf₂ y) rfl

/-- **Witness irrelevance for `Pic0.divPullback`.** -/
lemma divPullback_eq_of_witness_irrelevance
    (f : X → Y) (hf₁ hf₂ : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN₁ : ∀ y, (hf₁ y).toFinset.card = N)
    (hN₂ : ∀ y, (hf₂ y).toFinset.card = N) (D : Div0 Y) :
    Pic0.divPullback f hf₁ N hN₁ D = Pic0.divPullback f hf₂ N hN₂ D := by
  apply Subtype.ext
  rw [Pic0.divPullback_coe, Pic0.divPullback_coe]
  exact Div.fiberSum_eq_of_witness_irrelevance f hf₁ hf₂ (D : Div Y)

/-- **Witness irrelevance for `Pic0.pullback`.** -/
lemma pullback_eq_of_witness_irrelevance
    (f : X → Y) (hf₁ hf₂ : ∀ y, (f ⁻¹' {y}).Finite) (N : ℕ)
    (hN₁ : ∀ y, (hf₁ y).toFinset.card = N)
    (hN₂ : ∀ y, (hf₂ y).toFinset.card = N) (P : Pic0 Y) :
    Pic0.pullback f hf₁ N hN₁ P = Pic0.pullback f hf₂ N hN₂ P := by
  classical
  refine QuotientAddGroup.induction_on P ?_
  intro D
  rw [Pic0.pullback_mk, Pic0.pullback_mk]
  congr 1
  exact divPullback_eq_of_witness_irrelevance f hf₁ hf₂ N hN₁ hN₂ D

/-- **Witness-N irrelevance: two N values must agree** (when Y nonempty).
If both `hN₁ : ∀ y, card_toFinset = N₁` and `hN₂ : ∀ y, card_toFinset = N₂`
hold, then `N₁ = N₂` on Y nonempty. The cards equal `(hf y).toFinset.card`
for any chosen `y`, so they are forced. -/
lemma N_eq_of_constFibreCard_witnesses
    (f : X → Y) [Nonempty Y]
    (hf₁ hf₂ : ∀ y, (f ⁻¹' {y}).Finite) (N₁ N₂ : ℕ)
    (hN₁ : ∀ y, (hf₁ y).toFinset.card = N₁)
    (hN₂ : ∀ y, (hf₂ y).toFinset.card = N₂) :
    N₁ = N₂ := by
  classical
  obtain ⟨y⟩ := ‹Nonempty Y›
  have h₁ : (hf₁ y).toFinset.card = N₁ := hN₁ y
  have h₂ : (hf₂ y).toFinset.card = N₂ := hN₂ y
  have heq : (hf₁ y).toFinset = (hf₂ y).toFinset :=
    Set.Finite.toFinset_eq_of_set_eq (hf₁ y) (hf₂ y) rfl
  rw [heq] at h₁
  exact h₁.symm.trans h₂

end Pic0

end JacobianChallenge
