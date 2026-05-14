/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MMeromorphicHolomorphicEquivTransport
import JacobianChallenge.Manifold.RiemannSphereSimplePole

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `ExistsSimplePoleGermAtSomePoint X` from `HolomorphicEquiv X RiemannSphere`

The transport step in the genus-0 Riemann-Roch existence chain: given a
biholomorphism `e : X ≃ RS` (which is the analytic content of
uniformization at genus 0), pull the explicit simple-pole germ on `RS`
back to `X` via `e`. Since `mmeromorphicOrderAt` is invariant under
composition with a `HolomorphicEquiv`, the pulled-back function has a
simple pole at `e.symm ∞`.

## Construction

Set `p := e.symm ∞` and `ψ_X := RSSimplePole ∘ e : X → ℂ`.

* By `mmeromorphicOrderAt_holomorphicEquiv_comp` and
  `RSSimplePole_mmeromorphicAt_*`, `ψ_X` is `MMeromorphicAt` at every
  point.
* By the same transport, `mmeromorphicOrderAt 𝓘(ℂ,ℂ) ψ_X p =
  mmeromorphicOrderAt 𝓘(ℂ,ℂ) RSSimplePole ∞ = -1`.
* At any `y ≠ p`, `e y ≠ ∞`, so `mmeromorphicOrderAt 𝓘(ℂ,ℂ) ψ_X y =
  mmeromorphicOrderAt 𝓘(ℂ,ℂ) RSSimplePole (e y) ≥ 0` (`RSSimplePole`
  is holomorphic at finite points).

## Significance

This is the **uniformization step** in the genus-0 RR existence
discharge. The remaining classical input is the uniformization theorem
itself (`genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`),
which is multi-month classical work.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge.MeromorphicFunctionField

universe u

open JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The pulled-back simple-pole function -/

/-- The pulled-back simple-pole function: `RSSimplePole ∘ e : X → ℂ`. -/
noncomputable def pullbackSimplePole (e : HolomorphicEquiv X RiemannSphere) :
    X → ℂ :=
  RSSimplePole ∘ (e.toEquiv : X → RiemannSphere)

/-- Order at any `x : X` of the pulled-back function. -/
lemma pullbackSimplePole_orderAt
    (e : HolomorphicEquiv X RiemannSphere) (x : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (pullbackSimplePole e) x
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSSimplePole (e x) :=
  mmeromorphicOrderAt_holomorphicEquiv_comp e RSSimplePole x

/-- The pulled-back function is meromorphic at every `x : X`. -/
lemma pullbackSimplePole_mmeromorphicAt
    (e : HolomorphicEquiv X RiemannSphere) (x : X) :
    MMeromorphicAt 𝓘(ℂ, ℂ) (pullbackSimplePole e) x := by
  unfold pullbackSimplePole
  rw [MMeromorphicAt.holomorphicEquiv_comp_iff]
  -- At any point of RiemannSphere, RSSimplePole is meromorphic.
  induction e x using OnePoint.rec with
  | infty => exact RSSimplePole_mmeromorphicAt_infty
  | coe z => exact RSSimplePole_mmeromorphicAt_coe z

/-- The pulled-back function is `MMeromorphicOn` on `Set.univ`. -/
lemma pullbackSimplePole_mmeromorphicOn
    (e : HolomorphicEquiv X RiemannSphere) :
    MMeromorphicOn 𝓘(ℂ, ℂ) (pullbackSimplePole e) Set.univ := by
  intro x _
  exact pullbackSimplePole_mmeromorphicAt e x

/-! ## Order at the distinguished point `e.symm ∞` -/

/-- At `e.symm ∞`, the pulled-back function has order exactly `-1`
(simple pole transported from `∞ ∈ RS`). -/
lemma pullbackSimplePole_orderAt_symm_infty
    (e : HolomorphicEquiv X RiemannSphere) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (pullbackSimplePole e)
        (e.symm (∞ : RiemannSphere))
      = ((-1 : ℤ) : WithTop ℤ) := by
  rw [pullbackSimplePole_orderAt]
  -- Need: e (e.symm ∞) = ∞.
  have h_apply : e (e.symm (∞ : RiemannSphere)) = (∞ : RiemannSphere) :=
    e.toEquiv.apply_symm_apply (∞ : RiemannSphere)
  rw [h_apply]
  exact RSSimplePole_orderAt_infty

/-- At any `x ≠ e.symm ∞`, the pulled-back function has order `≥ 0`
(holomorphic at finite preimages of finite points). -/
lemma pullbackSimplePole_orderAt_nonneg_of_ne
    (e : HolomorphicEquiv X RiemannSphere)
    {x : X} (hx : x ≠ e.symm (∞ : RiemannSphere)) :
    0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) (pullbackSimplePole e) x := by
  rw [pullbackSimplePole_orderAt]
  -- e x ≠ ∞ (since x ≠ e.symm ∞ and e is injective).
  have h_ne : e x ≠ (∞ : RiemannSphere) := by
    intro h_eq
    apply hx
    -- From e x = ∞, derive x = e.symm ∞ by applying e.symm.
    have h_sym : e.symm (e x) = e.symm (∞ : RiemannSphere) := by rw [h_eq]
    -- `e.symm (e x) = x` definitionally via Equiv.symm_apply_apply.
    have h_round : e.symm (e x) = x := e.toEquiv.symm_apply_apply x
    rw [h_round] at h_sym
    exact h_sym
  -- Cases on `e x : RiemannSphere`.
  induction h_eq : e x using OnePoint.rec with
  | infty => exact absurd h_eq h_ne
  | coe z₀ => exact RSSimplePole_orderAt_coe_nonneg z₀

/-! ## Packaging and the headline theorem -/

/-- The bundled `MMer X` for the pulled-back simple-pole function. -/
noncomputable def pullbackSimplePoleMMer
    (e : HolomorphicEquiv X RiemannSphere) : MMer X where
  toFun := pullbackSimplePole e
  mmero := pullbackSimplePole_mmeromorphicOn e

/-- The germ. -/
noncomputable def pullbackSimplePoleGerm
    (e : HolomorphicEquiv X RiemannSphere) : MeromorphicFunctionGerm X :=
  MeromorphicFunctionGerm.mk (pullbackSimplePoleMMer e)

/-- The germ has order `-1` at `e.symm ∞`. -/
lemma pullbackSimplePoleGerm_orderAt_symm_infty
    (e : HolomorphicEquiv X RiemannSphere) :
    (pullbackSimplePoleGerm e).orderAt (e.symm (∞ : RiemannSphere))
      = ((-1 : ℤ) : WithTop ℤ) :=
  pullbackSimplePole_orderAt_symm_infty e

/-- The germ has order `≥ 0` at any other point. -/
lemma pullbackSimplePoleGerm_orderAt_nonneg_of_ne
    (e : HolomorphicEquiv X RiemannSphere)
    {x : X} (hx : x ≠ e.symm (∞ : RiemannSphere)) :
    0 ≤ (pullbackSimplePoleGerm e).orderAt x :=
  pullbackSimplePole_orderAt_nonneg_of_ne e hx

/-- The germ sits in `linearSystemGermDeltaP (e.symm ∞)`. -/
theorem pullbackSimplePoleGerm_mem_linearSystemGermDeltaP
    (e : HolomorphicEquiv X RiemannSphere) :
    pullbackSimplePoleGerm e ∈ linearSystemGermDeltaP (e.symm (∞ : RiemannSphere)) := by
  rw [mem_linearSystemGermDeltaP]
  refine ⟨?_, ?_⟩
  · -- Order at `e.symm ∞` ≥ -1 (in fact = -1).
    rw [pullbackSimplePoleGerm_orderAt_symm_infty]
  · -- Order off `e.symm ∞` ≥ 0.
    intro y hy
    exact pullbackSimplePoleGerm_orderAt_nonneg_of_ne e hy

/-- **`ExistsSimplePoleGermAtSomePoint X` from `Nonempty (HolomorphicEquiv
X RiemannSphere)`.** The genus-0 RR existence side reduces to
uniformization. -/
theorem existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS
    (h_equiv : Nonempty (HolomorphicEquiv X RiemannSphere)) :
    ExistsSimplePoleGermAtSomePoint X := by
  obtain ⟨e⟩ := h_equiv
  refine ⟨e.symm (∞ : RiemannSphere), pullbackSimplePoleGerm e, ?_, ?_⟩
  · exact pullbackSimplePoleGerm_mem_linearSystemGermDeltaP e
  · exact pullbackSimplePoleGerm_orderAt_symm_infty e

end JacobianChallenge.MeromorphicFunctionField

end
