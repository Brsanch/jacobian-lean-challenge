/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingMorphism
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackConst

set_option linter.unusedSectionVars false

/-! # Constant-curve-map `PeriodPairingMorphism`

For a constant curve map `fun _ : X => y₀ : X → Y`, the period-pairing
morphism is the zero morphism: the cycle pushforward is the zero
`AddMonoidHom` (the constant map collapses every cycle to a point) and
the adjunction reduces to `0 = 0` via
`HolomorphicOneForm.pullback_const` (sister chip already in tree).

Sister to `PeriodPairingMorphism.id` (identity case) and
`PeriodPairingMorphism.comp` (composition).
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Constant-curve-map period-pairing morphism.** For any
`data_X : PeriodPairingData X`, `data_Y : PeriodPairingData Y`, and any
target point `y₀ : Y`, the constant curve map `fun _ => y₀` gives the
zero period-pairing morphism.

The adjunction holds because both sides reduce to `0`: the LHS via the
zero cycle pushforward, and the RHS via `HolomorphicOneForm.pullback_const`. -/
noncomputable def PeriodPairingMorphism.const
    (data_X : PeriodPairingData X)
    (data_Y : PeriodPairingData Y)
    (y₀ : Y) :
    PeriodPairingMorphism data_X data_Y where
  f := fun _ => y₀
  contMDiff_f := contMDiff_const
  cyclePush := 0
  adjunction := by
    intro γ τ
    -- LHS: data_Y.pairing ((0 : H1_X →+ H1_Y) γ) τ
    --    = data_Y.pairing 0 τ        (zero AddMonoidHom applied is 0)
    --    = (0 : ... →ₗ[ℂ] ℂ) τ        (pairing AddMonoidHom maps 0 → 0)
    --    = 0.
    -- RHS: data_X.pairing γ (pullback (fun _ => y₀) _ τ)
    --    = data_X.pairing γ 0          (pullback_const)
    --    = 0                            (data_X.pairing γ is ℂ-linear).
    show data_Y.pairing ((0 : data_X.H1 →+ data_Y.H1) γ) τ
      = data_X.pairing γ (HolomorphicOneForm.pullback (fun _ : X => y₀)
          contMDiff_const τ)
    rw [HolomorphicOneForm.pullback_const, map_zero, AddMonoidHom.zero_apply,
      map_zero, LinearMap.zero_apply]

/-! ### Companion `@[simp]` lemmas -/

@[simp] theorem PeriodPairingMorphism.const_f
    (data_X : PeriodPairingData X)
    (data_Y : PeriodPairingData Y)
    (y₀ : Y) :
    (PeriodPairingMorphism.const data_X data_Y y₀).f = fun _ => y₀ := rfl

@[simp] theorem PeriodPairingMorphism.const_cyclePush
    (data_X : PeriodPairingData X)
    (data_Y : PeriodPairingData Y)
    (y₀ : Y) :
    (PeriodPairingMorphism.const data_X data_Y y₀).cyclePush = 0 := rfl

end JacobianChallenge

end
