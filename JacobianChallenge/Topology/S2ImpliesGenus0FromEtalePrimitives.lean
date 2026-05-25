/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.EtalePrimitivesGlobalSmooth
import JacobianChallenge.Topology.S2ImpliesGenus0FromPrimitiveExistenceUnconditional

set_option linter.unusedSectionVars false

/-! # `S2ImpliesGenus0 X` unconditionally on arbitrary X (Alt-B Chip 4e)

Closes the reverse leg of Item 14 (`S2ImpliesGenus0 X`) on arbitrary
compact connected complex 1-manifold X with
`IsManifold (𝓘(ℂ, ℂ)) ω X`. Combines:

* Étale-space arc (Chips 1-4d): on simply-connected `X`, every
  holomorphic 1-form `om` admits a smooth global primitive
  `globalPrimitive om x₀ : X → ℂ` (`contMDiff_globalPrimitive`).
* This file: shows `mfderiv (globalPrimitive om x₀) x = om.eval x` via
  the chart-local agreement (Chip 4d's
  `globalPrimitive_eqOn_localPrimitiveAtBallCenter_add_const`) +
  `Filter.EventuallyEq.mfderiv_eq` + `mfderiv_add` + `mfderiv_const` +
  cascade FTC `mfderiv_localPrimitiveAtBallCenter`.
* Composes with `s2ImpliesGenus0_of_primitiveExistence_uncond`.

## What this file ships

* `mfderiv_globalPrimitive` — `mfderiv (globalPrimitive om x₀) x = om.eval x`.
* `s2ImpliesGenus0_etalePrimitivesArc : S2ImpliesGenus0 X` — main
  theorem closing the reverse leg.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Filter

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **mfderiv of the global primitive equals `om.eval`.**
On the open neighborhood `u_x := globalSection om x₀ ⁻¹' B_x`,
`globalPrimitive` agrees with `localPrimitiveAtBallCenter om x +
(const c_x)` (Chip 4d). Pass to `mfderiv` via
`Filter.EventuallyEq.mfderiv_eq`, decompose via `mfderiv_add`, and
discharge the constant via `mfderiv_const = 0`. The remaining
`mfderiv (localPrimitiveAtBallCenter om x) x` equals `om.eval x` by
the cascade FTC (`mfderiv_localPrimitiveAtBallCenter`). -/
theorem mfderiv_globalPrimitive [SimplyConnectedSpace X]
    (om : HolomorphicOneForm X) (x₀ x : X) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (EtalePrimitives.globalPrimitive om x₀) x
      = om.eval x := by
  set c_x : ℂ := (EtalePrimitives.globalSection om x₀ x).primValue with hcx_def
  -- `globalPrimitive` agrees with `F_x + c_x` on the open nhd `u_x`.
  have h_evtEq :
      EtalePrimitives.globalPrimitive om x₀ =ᶠ[𝓝 x]
      (fun x' => localPrimitiveAtBallCenter om x x' + c_x) := by
    refine Filter.eventuallyEq_of_mem
      ((EtalePrimitives.globalSection_preimage_basicSheet_isOpen
          om x₀ x).mem_nhds
        (EtalePrimitives.globalSection_self_mem_basicSheet_preimage
          om x₀ x))
      ?_
    exact EtalePrimitives.globalPrimitive_eqOn_localPrimitiveAtBallCenter_add_const
            om x₀ x
  -- Bridge `mfderiv` via `EventuallyEq`.
  rw [h_evtEq.mfderiv_eq]
  have hx_in_src : x ∈ (convexBallChartAt x).source :=
    convexBallChartAt_x_mem_source x
  have h_F_diff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (localPrimitiveAtBallCenter om x) x :=
    localPrimitiveAtBallCenter_mdifferentiableAt om x x hx_in_src
  have h_const_diff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (fun _ : X => c_x) x :=
    mdifferentiable_const.mdifferentiableAt
  -- `mfderiv (F_x + const) = mfderiv F_x + 0 = mfderiv F_x`, via two intermediate
  -- equalities to avoid the unification headache around `0` in the CLM space.
  have h_sum_def :
      (fun x' => localPrimitiveAtBallCenter om x x' + c_x)
      = localPrimitiveAtBallCenter om x + (fun _ : X => c_x) :=
    rfl
  have h_mfd_eq :
      mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (fun x' => localPrimitiveAtBallCenter om x x' + c_x) x
        = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (localPrimitiveAtBallCenter om x) x := by
    rw [h_sum_def, mfderiv_add h_F_diff h_const_diff, mfderiv_const]
    exact add_zero _
  rw [h_mfd_eq, mfderiv_localPrimitiveAtBallCenter om x x hx_in_src]

/-! ## Reverse leg of Item 14 — closing theorem -/

/-- **`S2ImpliesGenus0 X` unconditionally on arbitrary X.** Composes the
étale-space arc (Chips 1-4d) for the smooth global primitive + Chip 4e's
`mfderiv_globalPrimitive` with the in-tree
`s2ImpliesGenus0_of_primitiveExistence_uncond`. This closes the reverse
leg of Item 14 on arbitrary compact connected complex 1-manifold `X`
with `IsManifold (𝓘(ℂ, ℂ)) ω X`. -/
theorem s2ImpliesGenus0_etalePrimitivesArc
    [IsManifold (𝓘(ℂ, ℂ)) ⊤ X] :
    S2ImpliesGenus0 X := by
  apply s2ImpliesGenus0_of_primitiveExistence_uncond
  intro h_sc om
  haveI : SimplyConnectedSpace X := h_sc
  -- Pick a basepoint `x₀ : X` (X is nonempty from ConnectedSpace).
  refine ⟨EtalePrimitives.globalPrimitive om (Classical.arbitrary X),
          EtalePrimitives.contMDiff_globalPrimitive om
            (Classical.arbitrary X),
          ?_⟩
  intro x
  exact (mfderiv_globalPrimitive om (Classical.arbitrary X) x).symm

end JacobianChallenge

end
