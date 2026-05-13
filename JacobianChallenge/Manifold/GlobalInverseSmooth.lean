/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalManifoldInverse

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Global `ω`-smoothness of `Function.invFun f` for an `ω`-smooth bijection (zz387)

For an `ω`-smooth, **bijective** `f : X → Y` between complex 1-manifolds, the
canonical inverse `Function.invFun f : Y → X` is itself `ω`-smooth.

Proof. At each `y : Y`, set `x := Function.invFun f y`. Then `f x = y` (right
inverse from surjectivity). Apply zz386 to obtain a local manifold inverse
`f_inv_local : Y → X` that is `ContMDiffAt … ω` at `f x = y` and satisfies
`f (f_inv_local y') = y'` eventually near `y`. Composing this eventual right-
inverse property with `f (Function.invFun f y') = y'` (also a right inverse)
and injectivity of `f` yields `f_inv_local =ᶠ[𝓝 y] Function.invFun f`.
`ContMDiffAt.congr_of_eventuallyEq` then transfers smoothness.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature changes to any pre-existing definition or theorem.
-/

noncomputable section

open scoped Topology Manifold ContDiff
open Function

namespace JacobianChallenge
namespace Manifold

universe u v

/-- **Global ω-smoothness of `Function.invFun f` for an `ω`-smooth bijection.** -/
theorem ContMDiff.contMDiff_invFun_of_bijective
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [Nonempty X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hbij : Function.Bijective f) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (Function.invFun f) := by
  intro y
  -- `x := invFun f y` is the (unique) preimage of `y`; `f x = y`.
  set x : X := Function.invFun f y with hx_def
  have hfx : f x = y := rightInverse_invFun hbij.surjective y
  have hinj : Function.Injective f := hbij.injective
  -- Pull out the zz386 local inverse at `x`.
  obtain ⟨f_inv_local, h_smooth_at_fx, h_left, _h_right⟩ :=
    ContMDiff.exists_local_manifold_inverse_of_injective hf hinj x
  -- `f_inv_local` and `Function.invFun f` agree on a nhd of `f x = y`.
  have h_agree :
      Function.invFun f =ᶠ[𝓝 (f x)] f_inv_local := by
    filter_upwards [h_left] with y' hy'
    -- `hy' : f (f_inv_local y') = y'`.
    have hf_inv : f (Function.invFun f y') = y' :=
      rightInverse_invFun hbij.surjective y'
    -- From `f (Function.invFun f y') = y' = f (f_inv_local y')`, injectivity gives
    -- the desired equality.
    exact hinj (hf_inv.trans hy'.symm)
  -- Transfer ContMDiffAt via congr.
  rw [← hfx]
  exact h_smooth_at_fx.congr_of_eventuallyEq h_agree

end Manifold
end JacobianChallenge

end
