/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.Degree

set_option diagnostics.threshold 100

/-! # `RegularValueWitness e` for a biholomorphism `e` has cardinality 1

For a biholomorphism `e : HolomorphicEquiv X Y`, every fibre
`e ⁻¹' {y}` is a singleton (since `e` is bijective). So any
`RegularValueWitness e` (and any `RegularValueWitnessReg e`) has
`card = 1`.

* `HolomorphicEquiv.fiber_eq_singleton` — `e ⁻¹' {y} = {e.symm y}`.
* `HolomorphicEquiv.RegularValueWitness_card_eq_one` —
  every `RegularValueWitness e` has card 1.
* `HolomorphicEquiv.RegularValueWitnessReg_card_eq_one` —
  same for `RegularValueWitnessReg`.

These are the cardinality-1 half of "biholomorphism has degree 1".
The remaining half is `Nonempty (RegularValueWitnessReg e)`, which
requires the chart-pullback derivative to be nonzero at the
biholomorphism preimage — provable in principle from
`mfderiv_symm_comp_mfderiv_self` (existing zz295) plus the chain rule
on the chart-pullback, but deferred to a later chip.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **Fibres of a biholomorphism are singletons.** -/
theorem HolomorphicEquiv.fiber_eq_singleton
    (e : HolomorphicEquiv X Y) (y : Y) :
    (e : X → Y) ⁻¹' {y} = {e.toEquiv.symm y} := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [Set.mem_singleton_iff]
    have : e.toEquiv.symm (e x) = e.toEquiv.symm y := by rw [hx]
    simpa using this
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hx]
    exact e.toEquiv.apply_symm_apply y

/-- **`RegularValueWitness` of a biholomorphism has card 1.** The
fibre is a singleton, so its `Set.Finite.toFinset` has card 1. -/
theorem HolomorphicEquiv.RegularValueWitness_card_eq_one
    (e : HolomorphicEquiv X Y)
    (w : JacobianChallenge.ContMDiff.RegularValueWitness (e : X → Y)) :
    w.card = 1 := by
  unfold ContMDiff.RegularValueWitness.card
  -- Goal: w.fiber_finite.toFinset.card = 1
  -- Route via `Set.encard`: encard = finset card for finite sets, and
  -- `encard_singleton` simplifies the rewritten singleton fibre to 1.
  have hFib : (e : X → Y) ⁻¹' {w.value} = {e.toEquiv.symm w.value} :=
    HolomorphicEquiv.fiber_eq_singleton e w.value
  have hEnc : ((e : X → Y) ⁻¹' {w.value}).encard = 1 := by
    rw [hFib]; exact Set.encard_singleton _
  have hLink :
      ((e : X → Y) ⁻¹' {w.value}).encard
        = (w.fiber_finite.toFinset.card : ℕ∞) :=
    Set.Finite.encard_eq_coe_toFinset_card w.fiber_finite
  -- Combine: card is the unique ℕ value with coe = encard.
  have h_cast : (w.fiber_finite.toFinset.card : ℕ∞) = (1 : ℕ∞) := by
    rw [← hLink]; exact hEnc
  exact_mod_cast h_cast

/-- **`RegularValueWitnessReg` of a biholomorphism has card 1.**
Follows from the plain `RegularValueWitness` version by unfolding the
`Reg` wrapper. -/
theorem HolomorphicEquiv.RegularValueWitnessReg_card_eq_one
    (e : HolomorphicEquiv X Y)
    (w : JacobianChallenge.ContMDiff.RegularValueWitnessReg (e : X → Y)) :
    w.card = 1 := by
  unfold ContMDiff.RegularValueWitnessReg.card
  exact HolomorphicEquiv.RegularValueWitness_card_eq_one e w.toWitness

end JacobianChallenge

end
