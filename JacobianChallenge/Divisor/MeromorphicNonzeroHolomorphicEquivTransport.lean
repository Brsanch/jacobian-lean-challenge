/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Divisor.HomeomorphTransport
import JacobianChallenge.Manifold.MMeromorphicHolomorphicEquivTransport

set_option linter.unusedSectionVars false

/-! # Transport of `MeromorphicNonzero` and `principalDivisorMap` through a `HolomorphicEquiv`

A biholomorphism `e : HolomorphicEquiv X Y` (analytic in both directions)
pulls back a `MeromorphicNonzero Y` to a `MeromorphicNonzero X` via
composition with `e`. The principal-divisor map is natural along this
transport:

  `principalDivisorMap (f.compHolomorphicEquiv e) = comap e.toHomeomorph (principalDivisorMap f)`.

In particular, `comap e.toHomeomorph` sends `PrincDiv Y` into `PrincDiv X`,
which (combined with `comap0Equiv` from `HomeomorphTransport.lean`) yields
the `Pic0` transport `Pic0 X ≃+ Pic0 Y` along a biholomorphism.

## What this file ships

* `MeromorphicNonzero.compHolomorphicEquiv` — the transported bundle.
* `principalDivisorMap_compHolomorphicEquiv` — the natural divisor
  identity.
* `comap_principalDivisorMap_mem_PrincDiv` — corollary: `comap` of a
  principal divisor is a principal divisor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y] [CompactSpace Y]
  [IsManifold (𝓘(ℂ, ℂ)) ω Y]

namespace MeromorphicNonzero

/-- **Pullback of `MeromorphicNonzero` along a biholomorphism.** -/
noncomputable def compHolomorphicEquiv
    (e : HolomorphicEquiv X Y) (f : MeromorphicNonzero Y) :
    MeromorphicNonzero X where
  toFun := f.toFun ∘ (e.toEquiv : X → Y)
  meromorphic := by
    intro x _
    exact (MMeromorphicAt.holomorphicEquiv_comp_iff e f.toFun x).mpr
      (f.meromorphic (e x) (Set.mem_univ _))
  nonvanishing_germ := by
    intro x
    rw [mmeromorphicOrderAt_holomorphicEquiv_comp e f.toFun x]
    exact f.nonvanishing_germ (e x)
  regular_continuousAt := by
    intro x h_order
    -- Pullback of order ≥ 0 at x is order ≥ 0 at e x.
    rw [mmeromorphicOrderAt_holomorphicEquiv_comp e f.toFun x] at h_order
    -- f is ContinuousAt (e x); e is ContinuousAt x; compose.
    have h_f_cont : ContinuousAt f.toFun (e x) := f.regular_continuousAt (e x) h_order
    have h_e_cmd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.toEquiv : X → Y) :=
      e.contMDiff_toFun
    have h_e_cont : ContinuousAt (e.toEquiv : X → Y) x := (h_e_cmd x).continuousAt
    exact h_f_cont.comp h_e_cont

@[simp] lemma compHolomorphicEquiv_toFun
    (e : HolomorphicEquiv X Y) (f : MeromorphicNonzero Y) :
    (f.compHolomorphicEquiv e).toFun = f.toFun ∘ (e.toEquiv : X → Y) := rfl

end MeromorphicNonzero

/-! ## Naturality of the principal-divisor map -/

/-- **Naturality of `principalDivisorMap` under biholomorphism.**

For `e : HolomorphicEquiv X Y` and `f : MeromorphicNonzero Y`,

  `principalDivisorMap (f.compHolomorphicEquiv e)
    = Div.comap e.toHomeomorph (principalDivisorMap f)`. -/
theorem principalDivisorMap_compHolomorphicEquiv
    (e : HolomorphicEquiv X Y) (f : MeromorphicNonzero Y) :
    principalDivisorMap (f.compHolomorphicEquiv e)
      = Div.comap e.toHomeomorph (principalDivisorMap f) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [principalDivisorMap_apply, Div.comap_apply, principalDivisorMap_apply]
  show JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ))
        (f.toFun ∘ (e.toEquiv : X → Y)) x
      = JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun (e x)
  unfold JacobianChallenge.MMeromorphicOn.orderFun
  rw [mmeromorphicOrderAt_holomorphicEquiv_comp e f.toFun x]

/-! ## `comap` sends `PrincDiv` into `PrincDiv` -/

/-- **`Div.comap e.toHomeomorph` sends a principal divisor to a principal
divisor.** Pulling back `principalDivisorMap f` by a biholomorphism `e`
gives the principal divisor of `f ∘ e`. -/
theorem Div.comap_principalDivisorMap_mem_PrincDiv
    (e : HolomorphicEquiv X Y) (f : MeromorphicNonzero Y) :
    Div.comap e.toHomeomorph (principalDivisorMap f) ∈ PrincDiv X := by
  rw [← principalDivisorMap_compHolomorphicEquiv e f]
  exact principalDivisorMap_mem_PrincDiv (f.compHolomorphicEquiv e)

end JacobianChallenge

end
