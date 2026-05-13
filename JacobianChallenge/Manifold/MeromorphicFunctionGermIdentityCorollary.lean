/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RRDimensionFormGerm

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Identity-theorem corollary on the germ field

This chip ships the **identity-theorem half** of the germ-side analog
of `JacobianChallenge.LiftToMeromorphicNonzero` from
`Topology/RRGenusZeroFinrankChain.lean`. Specifically, it packages the
identity theorem (`Manifold/MeromorphicFunctionField.lean`'s
`mmeromorphicOrderAt_ne_top_forall`) as the **germ-level statement**:

  *Any non-zero meromorphic-function germ has finite order at every
  point of `X`.*

This is the cleanly chip-sized piece of the germ-side rebuild. The
**other half** — building a representative `MeromorphicNonzero X`
satisfying `regular_continuousAt` at every order-`≥ 0` point —
requires a germ-canonicalisation construction (`germLimit` applied
pointwise globally) and a careful argument that the canonicalised
chart pullback is still meromorphic. The existing
`Divisor/PrincipalDivisor.lean`'s `germLimit_manifold_eventuallyEq_
punctured` uses `regular_continuousAt` of an *existing*
`MeromorphicNonzero` to bootstrap, which is circular for the
construction step. That second half is owed to a follow-up chip.

## What this file delivers

* `allOrdersNeTop` predicate at the germ level.
* `MeromorphicFunctionGerm.allOrdersNeTop_of_ne_zero` — direct
  application of the identity theorem already proved.
* The contrapositive equivalence
  `MeromorphicFunctionGerm.eq_zero_iff_exists_orderAt_eq_top`.
* `MeromorphicFunctionGerm.eq_zero_iff_forall_orderAt_eq_top` — under
  `ConnectedSpace X`, "essentially zero at one point" ⇔ "essentially
  zero everywhere" ⇔ "is the zero germ".
* `MeromorphicFunctionGerm.exists_rep_allOrders_ne_top_of_ne_zero` —
  germ-level rephrasing in representative form: for any non-zero
  germ, any `MMer` representative has all-orders-finite. This is the
  identity-theorem content packaged for downstream use.
* Cross-reference: any non-constant germ in `linearSystemGermDeltaP p`
  automatically has all orders finite (corollary).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## All-orders-finite predicate -/

/-- A germ `φ` has **all orders finite** if `φ.orderAt y ≠ ⊤` for every
`y : X`. This is the germ-level membership condition that an `MMer X`
representative must satisfy to qualify as a `MeromorphicNonzero X`
candidate (the `nonvanishing_germ` field). -/
def MeromorphicFunctionGerm.AllOrdersNeTop
    (φ : MeromorphicFunctionGerm X) : Prop :=
  ∀ y : X, φ.orderAt y ≠ ⊤

@[simp] lemma MeromorphicFunctionGerm.allOrdersNeTop_mk
    (f : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X).AllOrdersNeTop
      ↔ ∀ y : X, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤ := by
  rfl

/-! ## Identity-theorem application

The identity theorem (`mmeromorphicOrderAt_ne_top_forall` in
`Manifold/MeromorphicFunctionField.lean`) says: on a connected complex
1-manifold, if a globally meromorphic function has finite order at
*some* point, it has finite order at *every* point. Quotient-side: if
a germ is non-zero, then *some* representative has finite order at
some point; identity theorem upgrades that to all points; finite
order is germ-invariant, so it holds for any representative. -/

/-- **Identity-theorem corollary on the germ field.** Any non-zero
germ has finite order at every point of `X`. -/
theorem MeromorphicFunctionGerm.allOrdersNeTop_of_ne_zero
    {φ : MeromorphicFunctionGerm X} (hφ : φ ≠ 0) :
    φ.AllOrdersNeTop := by
  -- Pick a representative.
  rcases φ with ⟨f⟩
  -- From `[f] ≠ 0`, some y has finite order (else [f] would equal [0]).
  have h_exists : ∃ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤ := by
    by_contra h_all
    push_neg at h_all
    apply hφ
    show (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        = MeromorphicFunctionGerm.mk (0 : MMer X)
    apply Quotient.sound
    intro y
    show f.toFun =ᶠ[𝓝[≠] y] (0 : MMer X).toFun
    have h_zero_unfold : (0 : MMer X).toFun = (fun _ : X => (0 : ℂ)) := rfl
    rw [h_zero_unfold]
    exact (mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero f.toFun f.mmero y).mp
      (h_all y)
  -- Identity theorem upgrades to all y.
  exact mmeromorphicOrderAt_ne_top_forall f.toFun f.mmero h_exists

/-! ## Contrapositive forms -/

/-- **Identity theorem packaged as a direct implication.** On a
connected manifold, if a germ has `orderAt y = ⊤` at *some* `y`, then
the germ IS zero. -/
theorem MeromorphicFunctionGerm.eq_zero_of_exists_orderAt_eq_top
    {φ : MeromorphicFunctionGerm X} (h : ∃ y : X, φ.orderAt y = ⊤) :
    φ = 0 := by
  by_contra h_ne
  obtain ⟨y, hy⟩ := h
  exact MeromorphicFunctionGerm.allOrdersNeTop_of_ne_zero h_ne y hy

/-- The zero germ has `orderAt y = ⊤` at every `y`. -/
lemma MeromorphicFunctionGerm.zero_orderAt_eq_top (y : X) :
    (0 : MeromorphicFunctionGerm X).orderAt y = ⊤ := by
  show (MeromorphicFunctionGerm.mk (0 : MMer X) : MeromorphicFunctionGerm X).orderAt y = ⊤
  rw [MeromorphicFunctionGerm.orderAt_mk]
  show meromorphicOrderAt ((0 : MMer X).toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = ⊤
  have h_zero_comp : ((0 : MMer X).toFun ∘ (chartAt ℂ y).symm)
      = (fun _ : ℂ => (0 : ℂ)) := rfl
  rw [h_zero_comp, meromorphicOrderAt_const _ (0 : ℂ)]
  simp

/-- **Full equivalence:** a germ equals zero iff *some* (equivalently:
every) point has `orderAt = ⊤`. -/
theorem MeromorphicFunctionGerm.eq_zero_iff_exists_orderAt_eq_top
    (φ : MeromorphicFunctionGerm X) :
    φ = 0 ↔ ∃ y : X, φ.orderAt y = ⊤ := by
  refine ⟨?_, MeromorphicFunctionGerm.eq_zero_of_exists_orderAt_eq_top⟩
  intro h_zero
  haveI : Nonempty X := inferInstance
  have y : X := Classical.arbitrary X
  refine ⟨y, ?_⟩
  rw [h_zero]
  exact MeromorphicFunctionGerm.zero_orderAt_eq_top y

/-- Strong form: under `ConnectedSpace X`, "essentially zero at one
point" is equivalent to "essentially zero everywhere", which is
equivalent to being the zero germ. -/
theorem MeromorphicFunctionGerm.eq_zero_iff_forall_orderAt_eq_top
    (φ : MeromorphicFunctionGerm X) :
    φ = 0 ↔ ∀ y : X, φ.orderAt y = ⊤ := by
  constructor
  · intro h_zero y
    rw [h_zero]
    exact MeromorphicFunctionGerm.zero_orderAt_eq_top y
  · intro h_all
    -- Pick any y (X is nonempty since ConnectedSpace).
    haveI : Nonempty X := inferInstance
    have y : X := Classical.arbitrary X
    exact MeromorphicFunctionGerm.eq_zero_of_exists_orderAt_eq_top ⟨y, h_all y⟩

/-! ## Representative-form rephrasings

For any `MMer` representative of a non-zero germ, every chart-side
order is finite. This is the workhorse statement for downstream
canonicalisation (the regular-continuous step). -/

/-- For any non-zero germ, **every** `MMer` representative has all
orders finite. -/
theorem MeromorphicFunctionGerm.exists_rep_allOrders_ne_top_of_ne_zero
    {φ : MeromorphicFunctionGerm X} (hφ : φ ≠ 0) :
    ∀ (f : MMer X), φ = MeromorphicFunctionGerm.mk f →
      ∀ y : X, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤ := by
  intro f hf_eq y
  have h_all := MeromorphicFunctionGerm.allOrdersNeTop_of_ne_zero hφ y
  rw [hf_eq] at h_all
  show mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤
  exact h_all

/-! ## Non-constant germs in `linearSystemGermDeltaP` have all orders finite -/

/-- **Application to the RR thread:** any non-constant germ in
`linearSystemGermDeltaP p` has all orders finite. This is the
germ-side version of the "non-constant in L(δp) has bounded order"
half of the would-be `LiftToMeromorphicNonzero` (the other half is
`regular_continuousAt`, owed to a follow-up chip). -/
theorem MeromorphicFunctionGerm.allOrdersNeTop_of_mem_linearSystem_not_constants
    {p : X} {φ : MeromorphicFunctionGerm X}
    (_hφ_in : φ ∈ linearSystemGermDeltaP p)
    (hφ_not : φ ∉ constantsGerm X) :
    φ.AllOrdersNeTop := by
  -- A constant germ is, in particular, the zero germ when c = 0; non-constancy
  -- excludes membership in `constantsGerm = span ℂ {1}`. Note `0 = 0 • 1 ∈ span ℂ {1}`,
  -- so `φ ∉ span ℂ {1}` implies `φ ≠ 0`.
  apply MeromorphicFunctionGerm.allOrdersNeTop_of_ne_zero
  intro h_zero
  apply hφ_not
  rw [h_zero]
  exact Submodule.zero_mem _

end JacobianChallenge.MeromorphicFunctionField

end
