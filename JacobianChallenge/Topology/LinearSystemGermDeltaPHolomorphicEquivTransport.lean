/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicFunctionGermHolomorphicEquivPullback
import JacobianChallenge.Topology.LinearSystemGermDeltaP

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Transport of `linearSystemGermDeltaP` via `HolomorphicEquiv`

The germ-level pullback `compHolomorphicEquiv e` (from the prior chip)
preserves `orderAt` at corresponding points. Combined with the fact
that `e : X ≃ Y` is a bijection (so the off-pole quantifiers transport
between `∀ x ≠ p` and `∀ y ≠ e p`), this gives:

  `compHolomorphicEquiv e φ ∈ linearSystemGermDeltaP p
    ↔ φ ∈ linearSystemGermDeltaP (e p)`

i.e. the pullback restricts to a linear map between L(δp)'s.

After showing additive + scalar preservation, the restricted map is a
ℂ-linear map `linearSystemGermDeltaP (e p) →ₗ[ℂ] linearSystemGermDeltaP p`.

## Contents

* `MeromorphicFunctionGerm.compHolomorphicEquiv_zero/add/smul` —
  algebraic preservation.
* `MeromorphicFunctionGerm.compHolomorphicEquivLinearMap` — ℂ-linear
  map on germ fields.
* `IsBoundedByDeltaPGerm.compHolomorphicEquiv_iff` — L(δp) membership
  iff.
* `linearSystemGermDeltaP_compHolomorphicEquiv_iff` — Submodule version
  of the membership iff.
* `linearSystemGermDeltaPLinearMap_via_holomorphicEquiv` — the bundled
  ℂ-linear map between L(δp) submodules.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u v

open JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-! ## Algebraic preservation -/

/-- Pullback sends zero germ to zero germ. -/
@[simp] lemma MeromorphicFunctionGerm.compHolomorphicEquiv_zero
    (e : HolomorphicEquiv X Y) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e
        (0 : MeromorphicFunctionGerm Y)
      = (0 : MeromorphicFunctionGerm X) := by
  show MeromorphicFunctionGerm.compHolomorphicEquiv e
      (MeromorphicFunctionGerm.mk (0 : MMer Y))
    = MeromorphicFunctionGerm.mk (0 : MMer X)
  rw [MeromorphicFunctionGerm.compHolomorphicEquiv_mk]
  -- (MMer.compHolomorphicEquiv e 0).toFun = 0 ∘ e = 0.
  -- Reduce by Quotient.sound + pointwise equality on all of X.
  apply Quotient.sound
  intro x
  apply Filter.Eventually.of_forall
  intro y
  show (MMer.compHolomorphicEquiv e (0 : MMer Y)).toFun y = (0 : MMer X).toFun y
  rfl

/-- Pullback is additive. -/
lemma MeromorphicFunctionGerm.compHolomorphicEquiv_add
    (e : HolomorphicEquiv X Y) (φ ψ : MeromorphicFunctionGerm Y) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e (φ + ψ)
      = MeromorphicFunctionGerm.compHolomorphicEquiv e φ
          + MeromorphicFunctionGerm.compHolomorphicEquiv e ψ := by
  rcases φ with ⟨f⟩
  rcases ψ with ⟨g⟩
  show MeromorphicFunctionGerm.compHolomorphicEquiv e
      (MeromorphicFunctionGerm.mk f + MeromorphicFunctionGerm.mk g)
    = MeromorphicFunctionGerm.compHolomorphicEquiv e (MeromorphicFunctionGerm.mk f)
      + MeromorphicFunctionGerm.compHolomorphicEquiv e (MeromorphicFunctionGerm.mk g)
  rw [MeromorphicFunctionGerm.mk_add,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.mk_add]
  apply Quotient.sound
  intro x
  apply Filter.Eventually.of_forall
  intro y
  show (MMer.compHolomorphicEquiv e (f + g)).toFun y
      = (MMer.compHolomorphicEquiv e f + MMer.compHolomorphicEquiv e g).toFun y
  show ((f + g).toFun) ((e.toEquiv : X → Y) y)
      = (f.toFun ((e.toEquiv : X → Y) y)) + (g.toFun ((e.toEquiv : X → Y) y))
  show (f.toFun + g.toFun) ((e.toEquiv : X → Y) y)
      = f.toFun ((e.toEquiv : X → Y) y) + g.toFun ((e.toEquiv : X → Y) y)
  rfl

/-- Pullback is ℂ-linear. -/
lemma MeromorphicFunctionGerm.compHolomorphicEquiv_smul
    (e : HolomorphicEquiv X Y) (c : ℂ) (φ : MeromorphicFunctionGerm Y) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e (c • φ)
      = c • MeromorphicFunctionGerm.compHolomorphicEquiv e φ := by
  rcases φ with ⟨f⟩
  show MeromorphicFunctionGerm.compHolomorphicEquiv e
      (c • MeromorphicFunctionGerm.mk f)
    = c • MeromorphicFunctionGerm.compHolomorphicEquiv e (MeromorphicFunctionGerm.mk f)
  rw [MeromorphicFunctionGerm.mk_smul,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.mk_smul]
  apply Quotient.sound
  intro x
  apply Filter.Eventually.of_forall
  intro y
  show (MMer.compHolomorphicEquiv e (c • f)).toFun y
      = (c • MMer.compHolomorphicEquiv e f).toFun y
  show (c • f).toFun ((e.toEquiv : X → Y) y)
      = c • (f.toFun ((e.toEquiv : X → Y) y))
  show c • f.toFun ((e.toEquiv : X → Y) y) = c • f.toFun ((e.toEquiv : X → Y) y)
  rfl

/-! ## ℂ-linear map structure -/

/-- The pullback `compHolomorphicEquiv e` as a ℂ-linear map. -/
noncomputable def MeromorphicFunctionGerm.compHolomorphicEquivLinearMap
    (e : HolomorphicEquiv X Y) :
    MeromorphicFunctionGerm Y →ₗ[ℂ] MeromorphicFunctionGerm X where
  toFun := MeromorphicFunctionGerm.compHolomorphicEquiv e
  map_add' := MeromorphicFunctionGerm.compHolomorphicEquiv_add e
  map_smul' c φ := by
    show MeromorphicFunctionGerm.compHolomorphicEquiv e (c • φ)
      = c • MeromorphicFunctionGerm.compHolomorphicEquiv e φ
    exact MeromorphicFunctionGerm.compHolomorphicEquiv_smul e c φ

/-! ## `IsBoundedByDeltaPGerm` transport -/

/-- **`IsBoundedByDeltaPGerm` transport iff**:
`IsBoundedByDeltaPGerm p (compHolomorphicEquiv e φ) ↔ IsBoundedByDeltaPGerm (e p) φ`.
The bijection `e : X ≃ Y` shifts the quantifier `∀ x ≠ p` to `∀ y ≠ e p`,
and the `orderAt` preservation does the rest. -/
theorem IsBoundedByDeltaPGerm.compHolomorphicEquiv_iff
    (e : HolomorphicEquiv X Y) (p : X) (φ : MeromorphicFunctionGerm Y) :
    IsBoundedByDeltaPGerm p
        (MeromorphicFunctionGerm.compHolomorphicEquiv e φ)
      ↔ IsBoundedByDeltaPGerm (e p) φ := by
  unfold IsBoundedByDeltaPGerm
  constructor
  · rintro ⟨h_p, h_off⟩
    refine ⟨?_, ?_⟩
    · -- At `e p`: pullback at p has the same orderAt, ≥ -1.
      rw [MeromorphicFunctionGerm.compHolomorphicEquiv_orderAt] at h_p
      exact h_p
    · -- At y ≠ e p in Y: pullback at e.symm y has orderAt = φ.orderAt (e (e.symm y)) = φ.orderAt y.
      intro y hy
      -- Set x := e.symm y; then e x = y, x ≠ p (because if x = p, then y = e x = e p, contradiction).
      have h_apply : e (e.symm y) = y := e.toEquiv.apply_symm_apply y
      have h_off_at : 0 ≤ MeromorphicFunctionGerm.orderAt (e.symm y)
            (MeromorphicFunctionGerm.compHolomorphicEquiv e φ) := by
        apply h_off
        intro h_eq
        apply hy
        rw [← h_apply, h_eq]
      rw [MeromorphicFunctionGerm.compHolomorphicEquiv_orderAt] at h_off_at
      rw [h_apply] at h_off_at
      exact h_off_at
  · rintro ⟨h_ep, h_off_y⟩
    refine ⟨?_, ?_⟩
    · -- At p: orderAt = φ.orderAt (e p) ≥ -1.
      rw [MeromorphicFunctionGerm.compHolomorphicEquiv_orderAt]
      exact h_ep
    · -- At x ≠ p in X: orderAt = φ.orderAt (e x) ≥ 0 (since e x ≠ e p by injectivity).
      intro x hx
      rw [MeromorphicFunctionGerm.compHolomorphicEquiv_orderAt]
      apply h_off_y
      intro h_eq
      apply hx
      exact e.toEquiv.injective h_eq

/-- Submodule membership form. -/
theorem linearSystemGermDeltaP_compHolomorphicEquiv_iff
    (e : HolomorphicEquiv X Y) (p : X) (φ : MeromorphicFunctionGerm Y) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e φ ∈ linearSystemGermDeltaP p
      ↔ φ ∈ linearSystemGermDeltaP (e p) := by
  rw [mem_linearSystemGermDeltaP, mem_linearSystemGermDeltaP]
  exact IsBoundedByDeltaPGerm.compHolomorphicEquiv_iff e p φ

/-! ## Bundled `linearSystemGermDeltaP (e p) →ₗ[ℂ] linearSystemGermDeltaP p` -/

/-- The pullback `compHolomorphicEquiv e` restricts to a ℂ-linear map
`linearSystemGermDeltaP (e p) →ₗ[ℂ] linearSystemGermDeltaP p`. -/
noncomputable def linearSystemGermDeltaPLinearMap_via_holomorphicEquiv
    (e : HolomorphicEquiv X Y) (p : X) :
    linearSystemGermDeltaP (e p) →ₗ[ℂ] linearSystemGermDeltaP p :=
  ((MeromorphicFunctionGerm.compHolomorphicEquivLinearMap e).domRestrict
      (linearSystemGermDeltaP (e p))).codRestrict
    (linearSystemGermDeltaP p) (fun φ => by
      -- Goal: `((compHolomorphicEquivLinearMap e).domRestrict _) φ ∈ L(δp)`.
      -- Unfold to `compHolomorphicEquiv e φ.val ∈ L(δp)`.
      show MeromorphicFunctionGerm.compHolomorphicEquiv e (φ : MeromorphicFunctionGerm Y)
        ∈ linearSystemGermDeltaP p
      rw [linearSystemGermDeltaP_compHolomorphicEquiv_iff]
      exact φ.property)

end JacobianChallenge.MeromorphicFunctionField

end
