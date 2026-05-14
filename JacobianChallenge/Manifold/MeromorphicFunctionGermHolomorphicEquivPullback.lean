/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MMeromorphicHolomorphicEquivTransport
import JacobianChallenge.Manifold.MeromorphicFunctionField
import JacobianChallenge.Topology.LinearSystemGermDeltaP

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pullback on `MeromorphicFunctionGerm` via a `HolomorphicEquiv`

A biholomorphism `e : HolomorphicEquiv X Y` induces a pullback ring
homomorphism on germ fields by composition:
`(f : MMer Y) ↦ (f.toFun ∘ e : X → ℂ)`. The meromorphicity of the
result follows from `MMeromorphicAt.holomorphicEquiv_comp_iff`, and
the descent to `MeromorphicFunctionGerm Y → MeromorphicFunctionGerm X`
preserves the punctured-neighborhood equivalence because `e` is a
homeomorphism (continuous + open).

The orderAt is preserved at corresponding points
`(MFG.compHolomorphicEquiv e φ).orderAt x = φ.orderAt (e x)`.

## Contents

* `MMer.compHolomorphicEquiv` — pullback on `MMer`.
* `MMer.compHolomorphicEquiv_toFun` — definitional unfolding.
* `MeromorphicFunctionGerm.compHolomorphicEquiv` — descent to germs.
* `MeromorphicFunctionGerm.compHolomorphicEquiv_mk` — descent action on
  `mk`.
* `MeromorphicFunctionGerm.compHolomorphicEquiv_orderAt` — preserves
  `orderAt`.

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

/-! ## Pullback on `MMer` -/

/-- The pullback of a bundled meromorphic function `f : MMer Y` via a
`HolomorphicEquiv X Y`: precompose with `e`. -/
noncomputable def MMer.compHolomorphicEquiv
    (e : HolomorphicEquiv X Y) (f : MMer Y) : MMer X where
  toFun := f.toFun ∘ (e.toEquiv : X → Y)
  mmero := by
    intro x _
    rw [MMeromorphicAt.holomorphicEquiv_comp_iff]
    exact f.mmero (e x) (Set.mem_univ _)

@[simp] lemma MMer.compHolomorphicEquiv_toFun
    (e : HolomorphicEquiv X Y) (f : MMer Y) :
    (MMer.compHolomorphicEquiv e f).toFun = f.toFun ∘ (e.toEquiv : X → Y) :=
  rfl

/-! ## Punctured-nhd EvEq is preserved -/

/-- For a homeomorphism (forward direction of a `HolomorphicEquiv`),
the punctured-nhd EvEq at `e x` pulls back to a punctured-nhd EvEq at
`x`. -/
lemma MMer.compHolomorphicEquiv_germSetoid_respect
    (e : HolomorphicEquiv X Y) {f g : MMer Y}
    (hfg : ∀ y, f.toFun =ᶠ[𝓝[≠] y] g.toFun) :
    ∀ x, (MMer.compHolomorphicEquiv e f).toFun
            =ᶠ[𝓝[≠] x] (MMer.compHolomorphicEquiv e g).toFun := by
  intro x
  show (f.toFun ∘ (e.toEquiv : X → Y)) =ᶠ[𝓝[≠] x] (g.toFun ∘ (e.toEquiv : X → Y))
  have h_cts : ContinuousAt (e.toEquiv : X → Y) x :=
    (e.contMDiff_toFun x).continuousAt
  have h_inj : Function.Injective (e.toEquiv : X → Y) := e.toEquiv.injective
  -- Convert the source EvEq at `e x` to set form.
  have h_at_ex : f.toFun =ᶠ[𝓝[≠] (e x)] g.toFun := hfg (e x)
  rw [Filter.eventuallyEq_iff_exists_mem] at h_at_ex
  obtain ⟨S, hS_mem, hS_eq⟩ := h_at_ex
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hS_mem
  obtain ⟨U, hU_nhds, hU_sub⟩ := hS_mem
  -- Build the pulled-back EvEq.
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨(e.toEquiv : X → Y) ⁻¹' U ∩ {x}ᶜ, ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨(e.toEquiv : X → Y) ⁻¹' U, h_cts.preimage_mem_nhds hU_nhds,
      fun y hy => ⟨hy.1, hy.2⟩⟩
  · intro y hy
    show f.toFun ((e.toEquiv : X → Y) y) = g.toFun ((e.toEquiv : X → Y) y)
    refine hS_eq (hU_sub ⟨hy.1, ?_⟩)
    -- y ≠ x ⇒ e y ≠ e x by injectivity.
    intro h_eq
    have hy_ne : y ≠ x := hy.2
    apply hy_ne
    exact h_inj h_eq

/-! ## Descent to `MeromorphicFunctionGerm` -/

/-- The pullback `MeromorphicFunctionGerm Y → MeromorphicFunctionGerm
X` via composition with `e`. -/
noncomputable def MeromorphicFunctionGerm.compHolomorphicEquiv
    (e : HolomorphicEquiv X Y) :
    MeromorphicFunctionGerm Y → MeromorphicFunctionGerm X :=
  Quotient.lift (s := germSetoid Y)
    (fun f => MeromorphicFunctionGerm.mk (MMer.compHolomorphicEquiv e f))
    (by
      intro f g hfg
      apply Quotient.sound
      exact MMer.compHolomorphicEquiv_germSetoid_respect e hfg)

@[simp] lemma MeromorphicFunctionGerm.compHolomorphicEquiv_mk
    (e : HolomorphicEquiv X Y) (f : MMer Y) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e
        (MeromorphicFunctionGerm.mk f)
      = MeromorphicFunctionGerm.mk (MMer.compHolomorphicEquiv e f) := rfl

/-! ## Order is preserved -/

/-- The germ-level pullback preserves `orderAt` at corresponding points. -/
theorem MeromorphicFunctionGerm.compHolomorphicEquiv_orderAt
    (e : HolomorphicEquiv X Y) (φ : MeromorphicFunctionGerm Y) (x : X) :
    MeromorphicFunctionGerm.orderAt x
        (MeromorphicFunctionGerm.compHolomorphicEquiv e φ)
      = MeromorphicFunctionGerm.orderAt (e x) φ := by
  rcases φ with ⟨f⟩
  -- After rcases, φ is `Quot.mk _ f`, which is `mk f` definitionally.
  show MeromorphicFunctionGerm.orderAt x
      (MeromorphicFunctionGerm.compHolomorphicEquiv e (MeromorphicFunctionGerm.mk f))
    = MeromorphicFunctionGerm.orderAt (e x) (MeromorphicFunctionGerm.mk f)
  rw [MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.orderAt_mk,
      MeromorphicFunctionGerm.orderAt_mk]
  rw [MMer.compHolomorphicEquiv_toFun]
  exact mmeromorphicOrderAt_holomorphicEquiv_comp e f.toFun x

end JacobianChallenge.MeromorphicFunctionField

end
